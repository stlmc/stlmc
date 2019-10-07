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
        this._tag = "#proposition"+this._index;
        this._jd = _jd;

    }

    /**
     * d3.select must be invoke after Reactjs's componentdidmount called.
     * This will get DOM elements well.
     */
    setCanvas() {
        // set main canvas
        this.canvas = d3.select(this._tag).append("svg").attr("id", "prop_svg")
            .attr("width", this._size.width).attr("height", this._size.height);

        // set data canvas
        //this.setDataCanvas();
        this.setCanvasAxis();
        // set prop canvas
        this.setPropCanvas();
    }


    loadGraph(isEmpty, maxX, data, xrange) {
        this.dataXrange = maxX;
        this.xrange = xrange;
        console.log(xrange);
        this.setCanvas();
        //d3.selectAll("#main_svg").remove();
        //d3.selectAll("#tooltip").remove();
        if (!isEmpty) {
            // Get original data's x's and y's extent.
            // Will slow loading since json.data.xRange() itself need lots of calculations.
            // Need to be removed soon.


            // Add scale error to make lines fit the view box.
            // TODO: Update formula for error. Divide by 10 is not optimal.
            let XscaleError = (this.dataXrange[1] - this.dataXrange[0]) / 10;


            // Set scale function for x.
            // Clipping margin does the correction of calculate length of x axis.
            // X axis is move this.x_clip_margin by below code.
            this.dataCanvasXscale = d3.scaleLinear()
                .domain([this.dataXrange[0], this.dataXrange[1] + XscaleError])
                .range([0, this._size.width]);



            // update when redraw, remove previous proposition graph.
            //this.propCanvas.selectAll("#propGraphGroup").remove();
            //this.propCanvas.selectAll("#focusCircle2").remove();


            this.propGraph = this.propCanvasBack
                .append("g")
                .attr("id", "propGraph")
                .selectAll(".propGraphData")
                .data(data)
                .enter();

            let scaleX = this.dataCanvasXscale;
            let scaleY = this.propCanvasYscale;

            // set proposition graph line generator
            this.propLineGenerator = d3.line()
                .x(function (d) {
                    return scaleX(d[0]);
                })
                .y(function (d) {
                    return scaleY(d[1]);
                }).curve(d3.curveMonotoneX);

            /**
             * this is actual data of proposition graph
             */
            this.propGraph
                .append("path")
                .attr("d", (d) => {
                    return this.propLineGenerator(d);
                })
                .attr("class", "propGraphData")
                .attr("stroke", "red")
                .attr("stroke-width", 1.5);
        }

    }


    /**
     * Setting axis for the Proposition Canvas needs.
     * */
    setCanvasAxis() {


        // Get original data's x's and y's extent.
        // Will slow loading since json.data.xRange() itself need lots of calculations.
        // Need to be removed soon.
        //this.dataXrange = this.data.xRange();


        // Add scale error to make lines fit the view box.
        // TODO: Update formula for error. Divide by 10 is not optimal.
        let XscaleError = (this.dataXrange[1] - this.dataXrange[0]) / 10;


        // Set scale function for x.
        // Clipping margin does the correction of calculate length of x axis.
        // X axis is move this.x_clip_margin by below code.
        this.dataCanvasXscale = d3.scaleLinear()
            .domain([this.dataXrange[0], this.dataXrange[1] + XscaleError])
            .range([0, this._size.width]);


    }



    /**
     * prop canvas has 2 cavases innerly, back prop canvas does nothing
     * and front prop canvas is for user interactions (such as, zooming, clipping, mouse moving etc)
     *
     * Need to use propCanvasFront for interactions and propCanvas(back) for data showing or redraw, update.
     */
    setPropCanvas() {

        //set clipping path

        this.canvas.append("clipPath")
            .attr("id", "propCanvasClip"+this._index)
            .append("rect")
            .attr("width", this._size.width)
            .attr("height", this.data_viewer_height);


        // set canvas front
        this.propCanvasBack = this.canvas.append("g")
            .attr("id", "propCanvasBack"+this._index)
            .attr("clip-path", "url(#propCanvasClip"+this._index+")")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (-(this._size.height - this.data_viewer_height) + 1) + ")");


        // set scale function for y
        // 0: none, 1: false, 2: true, 3:none
        this.propCanvasYscale =
            d3.scaleLinear()
                .domain([0, 3])
                .range([this.data_viewer_height, 0]);




        // Add interval lines.
        this.propCanvasIntervalLines = this.propCanvasBack.append("g")
            .attr("id", "propCanvasIntervalLinesBase")
            .attr("transform", "translate(" + 0 + "," + (4) + ")");

        // tickValues is actual data line
        // e.g) if you put [1, 2] in the tickValues than, it will draw line to x:1 and x:2.
        this.propCanvasIntervalLines.call(d3.axisBottom(this.dataCanvasXscale).tickValues(this.xrange).tickSize(this._size.height).tickPadding(3).tickFormat(() => {
            return ""
        })).select(".domain").remove();



        // Add x axis for propCanvas.
        this.propCanvasXaxis = this.canvas.append("g")
            .attr("id", "propCanvasXaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this.data_viewer_height + 1) + ")")
            .call(d3.axisBottom(this.dataCanvasXscale));

        // Add y axis.
        this.propCanvasYaxis = this.canvas.append("g")
            .attr("id", "propCanvasYaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + 1 + ")");

        this.propCanvasYaxis.call(d3.axisLeft(this.propCanvasYscale).ticks(4).tickFormat(
            (d) => {
                if (d === 1) {
                    return "false"
                } else if (d === 2) {
                    return "true"
                } else {
                    return " "
                }
            }));
    }

    setdata(jd) {
        if (!jd.isEmpty()) {
            this.json = jd;
        }

    }

}

export {PropositionRenderer};