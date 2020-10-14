import * as d3 from 'd3';
import $ from "jquery";
import "./MainRenderer.scss";

class PropositionRenderer {


    constructor(
        _size,
        _margin_viewer,
        _index,
        _jd = '',
    ) {
        this.axis_delta = 50.0;
        this.x_clip_margin = 50.0;

        // actual data point viewers height.
        this.data_viewer_height = 60.0;

        this._size = _size;
        this._margin_viewer = _margin_viewer;
        this._index = _index;
        this._tag = "#proposition" + this._index;
        this._jd = _jd;

    }

    clear(){
        d3.select(this._tag).selectAll("#prop_svg").remove();
    }

    loadGraph(maxX, data, xrange) {
        this.dataXrange = maxX;
        this.xrange = xrange;

        d3.select(this._tag).selectAll("#prop_svg").remove();

        // set main canvas
        this.canvas = d3.select(this._tag).append("svg").attr("id", "prop_svg")
            .attr("width", this._size.width).attr("height", this._size.height);

        // set canvas front
        this.propCanvas = this.canvas.append("g")
            .attr("id", "propCanvas" + this._index)
            .attr("clip-path", "url(#propCanvasClip" + this._index + ")")
            .attr("transform", "translate(" + this.x_clip_margin + "," + 0 + ")");

        // set data canvas
        // Add scale error to make lines fit the view box.
        // TODO: Update formula for error. Divide by 10 is not optimal.
        let XscaleError = (this.dataXrange[1] - this.dataXrange[0]) / 10;


        // Set scale function for x.
        // Clipping margin does the correction of calculate length of x axis.
        // X axis is move this.x_clip_margin by below code.
        this.Xscale = d3.scaleLinear()
            .domain([this.dataXrange[0], this.dataXrange[1] + XscaleError])
            .range([0, this._size.width]);

        // set scale function for y
        // 0: none, 1: false, 2: true, 3:none
        this.Yscale =
            d3.scaleLinear()
                .domain([0, 3])
                .range([this.data_viewer_height, 0]);



        this.canvas.append("clipPath")
            .attr("id", "propCanvasClip" + this._index)
            .append("rect")
            .attr("width", this._size.width)
            .attr("height", this.data_viewer_height);




        let scaleX = this.Xscale;
        let scaleY = this.Yscale;


        // Add interval lines.
        this.propCanvasIntervalLines = this.propCanvas.append("g")
            .attr("id", "propCanvasIntervalLines")
            //.attr("transform", "translate(" + 0 + "," + (-50) + ")");

        // tickValues is actual data line
        // e.g) if you put [1, 2] in the tickValues than, it will draw line to x:1 and x:2.
        this.propCanvasIntervalLines.call(d3.axisBottom(scaleX).tickValues(this.xrange).tickSize(this._size.height).tickPadding(3).tickFormat(() => {
            return ""
        })).select(".domain").remove();


        // Add x axis for propCanvas.
        this.propCanvasXaxis = this.canvas.append("g")
            .attr("id", "propCanvasXaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this.data_viewer_height + 1) + ")")
            .call(d3.axisBottom(scaleX));

        // Add y axis.
        this.propCanvasYaxis = this.canvas.append("g")
            .attr("id", "propCanvasYaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + 1 + ")");

        this.propCanvasYaxis.call(d3.axisLeft(scaleY).ticks(4).tickFormat(
            (d) => {
                if (d === 1) {
                    return "false"
                } else if (d === 2) {
                    return "true"
                } else {
                    return " "
                }
            }));

        // update when redraw, remove previous proposition graph.
        this.propGraph = this.propCanvas
            .selectAll(".propLines")
            .append("g")
            .data(data)
            .enter();


        // set proposition graph line generator
        this.propLineGenerator = d3.line()
            .x(function (d) {
                return scaleX(d[0]);
            })
            .y(function (d) {
                return scaleY(d[1]);
            }).curve(d3.curveMonotoneX);

        let propLineG = this.propLineGenerator;
        /**
         * this is actual data of proposition graph
         */
        this.propGraph
            .append("path")
            .attr("d", (d) => {
                return propLineG(d);
            })
            .attr("class", "propLines")
            .attr("stroke", "red")
            .attr("stroke-width", 1.5);

    }

}

export {PropositionRenderer};