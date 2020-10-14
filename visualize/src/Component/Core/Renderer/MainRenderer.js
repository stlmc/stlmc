import * as d3 from 'd3';
import $ from "jquery";
import "./MainRenderer.scss";

class Renderer {


    constructor(
        _size,
        _margin_viewer,
        _index,
        _jd = ''
    ) {
        this.axis_delta = 50.0;
        this.x_clip_margin = 50.0;

        this._size = _size;
        this._margin_viewer = _margin_viewer;
        this._index = _index;
        this._tag = "#graph" + this._index;
        this._jd = _jd;
        this.data_viewer_height = this._size.height - 20.0;
    }


    get graph() {
        return this._graph;
    }

    set graph(graph) {
        this._graph = graph;
    }

    clear() {
        d3.select(this._tag).selectAll("#main_svg").remove();
    }

    loadGraph(maxX, maxY, l, xdata, pdata, vardict, modeSize, subXscale, subYscale) {
        this.refData = l;
        d3.select(this._tag).selectAll("#main_svg").remove();
        d3.select(this._tag).selectAll("#main_svg_info").remove();

        this.canvas = d3.select(this._tag).append("svg").attr("id", "main_svg")
            .attr("width", this._size.width).attr("height", this._size.height);

        let fps = d3.select("#graph span");

        let t0 = Date.now(), t1;

        d3.timer(function () {

            t1 = Date.now();
            fps.text(Math.round(1000 / (t1 - t0)) + " fps");
            t0 = t1;
        });

        // set data canvas
        this.graphCanvas = this.canvas.append("g")
            .attr("id", "graphCanvas" + this._index)
            .attr("clip-path", "url(#graphCanvasClip" + this._index + ")")
            .attr("transform", "translate(" + this.x_clip_margin + "," + 0 + ")");


        this.canvas.append("clipPath")
            .attr("id", "graphCanvasClip" + this._index)
            .append("rect")
            .attr("width", this._size.width)
            .attr("height", this.data_viewer_height);

        this.graphCanvasFront =
            this.graphCanvas.append("g");

        // Color scale for line plot in dataCanvas.
        // This will automatically add colors to your lines.
        this.colorScale = d3.scaleOrdinal(d3.schemeCategory10);


        // Get original data's x's and y's extent.
        // Will slow loading since json.data.xRange() itself need lots of calculations.
        // Need to be removed soon.
        this.dataXrange = maxX;
        this.dataYrange = maxY;

        // Add scale error to make lines fit the view box.
        // TODO: Update formula for error. Divide by 10 is not optimal.
        let XscaleError = (this.dataXrange[1] - this.dataXrange[0]) / 10;
        let YscaleError = (this.dataYrange[1] - this.dataYrange[0]) / 10;

        // Set scale function for x.
        // Clipping margin does the correction of calculate length of x axis.
        // X axis is move this.x_clip_margin by below code.
        this.dataCanvasXscale = d3.scaleLinear()
            .domain([this.dataXrange[0], this.dataXrange[1] + XscaleError])
            .range([0, this._size.width]);

        // Set scale function for y.
        // This process will do the same thing as x.
        this.dataCanvasYscale = d3.scaleLinear()
            .domain([this.dataYrange[0] - YscaleError, this.dataYrange[1] + YscaleError])
            .range([this.data_viewer_height, 0]);

        this.dataCanvasXscaleZoom = this.dataCanvasXscale;
        this.dataCanvasYscaleZoom = this.dataCanvasYscale;

        // Add scaling function generators for x and y.
        let make_y_grid = () => {
            return d3.axisBottom(this.dataCanvasXscale);
        };
        let make_x_grid = () => {
            return d3.axisLeft(this.dataCanvasYscale);
        };

        // Add this Grid xis first. If not, left y axis will overlap with grid axis.
        this.graphCanvasXaxisGrid = this.graphCanvas.append("g")
            .attr("id", "graphCanvasXaxisGrid" + this._index)
            .attr("class", "XaxisGrid");

        this.graphCanvasXaxisGrid.call(make_y_grid()
            .tickSize(this._size.height)
            .tickPadding(10)
            .tickFormat(() => {
                return "";
            }))
            .select(".domain").remove();

        this.graphCanvasYaxisGrid = this.graphCanvas.append("g")
            .attr("id", "graphCanvasYaxisGrid" + this._index)
            .attr("class", "YaxisGrid");

        // -this._size.width will mirroring the position.
        this.graphCanvasYaxisGrid.call(make_x_grid()
            .tickSize(-this._size.width)
            .tickPadding(10)
            .tickFormat(() => {
                return "";
            }))
            .select(".domain").remove();

        // Add clipping path.
        // If you are adding clipping path without margin, your zero of your axis will get lost.
        // Add x and y axis to dataCanvas.
        this.graphCanvasXaxis = this.canvas.append("g")
            .attr("id", "graphCanvasXaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this.data_viewer_height + 1) + ")")
            .call(d3.axisBottom(this.dataCanvasXscale));

        this.graphCanvasYaxis = this.canvas.append("g")
            .attr("id", "graphCanvasYaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + 1 + ")")
            .call(d3.axisLeft(this.dataCanvasYscale));


        // Add zoom function to dataCanvas
        this.zoom = d3.zoom()
            .extent([[0, 0], [this._size.width, this.data_viewer_height]])
            .scaleExtent([1, Infinity])
            .translateExtent([[0, -this.dataYrange[1]], [Infinity, Infinity]])
            .on("zoom", () => {

                // Update scale functions to zoomed ones.
                this.dataCanvasXscaleZoom = d3.event.transform.rescaleX(this.dataCanvasXscale);
                this.dataCanvasYscaleZoom = d3.event.transform.rescaleY(this.dataCanvasYscale);

                // Update axis.
                this.graphCanvasXaxis.call(d3.axisBottom(this.dataCanvasXscaleZoom));
                this.graphCanvasYaxis.call(d3.axisLeft(this.dataCanvasYscaleZoom));

                d3.selectAll("#propCanvasXaxis").call(d3.axisBottom(this.dataCanvasXscaleZoom));
                d3.selectAll("#propCanvasIntervalLines").call(d3.axisBottom(this.dataCanvasXscaleZoom).tickValues(pdata).tickSize(100).tickPadding(3).tickFormat(() => {
                    return ""
                })).select(".domain").remove();

                d3.selectAll("#modeCanvasXaxis").call(d3.axisBottom(this.dataCanvasXscaleZoom));
                d3.selectAll("#modeCanvasIntervalLines").call(d3.axisBottom(this.dataCanvasXscaleZoom).tickValues(pdata).tickSize(100).tickPadding(3).tickFormat(() => {
                    return ""
                })).select(".domain").remove();


                this.propCanvasYscale =
                    d3.scaleLinear()
                        .domain([0, 3])
                        .range([60.0, 0]);


                // Make new line scale functions using latest scale functions.
                this.lineGenerator = d3.line()
                    .x((d) => {
                        return this.dataCanvasXscaleZoom(d[0]);
                    })
                    .y((d) => {
                        return this.dataCanvasYscaleZoom(d[1]);
                    })
                    .curve(d3.curveMonotoneX);

                this.lineGenerator2 = d3.line()
                    .x((d) => {
                        return this.dataCanvasXscaleZoom(d[0]);
                    })
                    .y((d) => {
                        return this.propCanvasYscale(d[1]);
                    })
                    .curve(d3.curveMonotoneX);


                d3.selectAll(".propLines")
                    .attr("d", (d) => {
                        return this.lineGenerator2(d);
                    });


                // update mode variable scale
                for(let i = 0; i < modeSize; i++){
                    let lineG = d3.line()
                        .x((d) => {
                            return this.dataCanvasXscaleZoom(d[0]);
                        })
                        .y((d) => {
                            return subYscale[i](d[1]);
                        }).curve(d3.curveMonotoneX);

                    d3.selectAll("#modeLines"+i)
                        .attr("d", (d)=>{
                            return lineG(d);
                        })
                }

                // Update lines positions.
                // Update position first and then rendering it
                this.lineGraph.selectAll(".lines")
                    .each((d) => {
                        d.newX = this.lineGenerator(d.data);
                    });

                this.lineGraph.selectAll(".lines")
                    .attr("d", (d) => {
                        return d.newX;
                    });

            });

        this.tooltip = d3.select(this._tag)
            .append("div")
            .attr("id", "tooltip")
            .style("position", "absolute")
            .style("visibility", "hidden")
            .style("background-color", "rgba(0, 0, 0, 0.7)")
            .style("border", "solid")
            .style("border-width", "1px")
            .style("border-radius", "5px")
            .style("padding", "10px");



        this.drawGraph(l, xdata, vardict);

    }


    drawGraph(l, xdata, vardict) {

        let color = d3.scaleOrdinal()
            .domain(vardict)
            .range(d3.schemeTableau10);

        let newDataList = [];
        let nameList = [];
        for(let [k, v] of l){
            let elem = {
                name: k,
                data: v
            };
            newDataList.push(elem);
            nameList.push(k);
        }
        let infoHeight = nameList.length * 30;


        this.InfoCanvas = d3.select(this._tag).append("svg").attr("id", "main_svg_info")
            .attr("width", this._size.width).attr("height", infoHeight);

        this.InfoCanvas.selectAll("dots")
            .data(nameList)
            .enter()
            .append("circle")
            .attr("cx", 20)
            .attr("cy", (d, i) => {return 15 + i * 25})
            .attr("r", 7)
            .style("fill", (d)=> { return color(d) });


        // Add one dot in the legend for each name.
        this.InfoCanvas.selectAll("labels")
            .data(nameList)
            .enter()
            .append("text")
            .attr("x", 40)
            .attr("y", function(d,i){ return 15 + i*25}) // 100 is where the first dot appears. 25 is the distance between dots
            .style("fill", function(d){ return color(d)})
            .text(function(d){ return d})
            .attr("text-anchor", "left")
            .style("alignment-baseline", "middle");



        let dataCanvasXscale = this.dataCanvasXscale;
        let dataCanvasYscale = this.dataCanvasYscale;
        this.lineGenerator = d3.line()
            .x(function (d) {
                return dataCanvasXscale(d[0]);
            })
            .y(function (d) {
                return dataCanvasYscale(d[1]);
            }).curve(d3.curveMonotoneX);

        // add line to dataCanvas front where clipping path is added.
        this.lineGraph = this.graphCanvas
            .selectAll(".lines")
            .append("g")
            .data(newDataList)
            .enter();

        this.lineGraph.append("path")
            .attr("d", (d) => {
                return this.lineGenerator(d.data);
            })
            .attr("class", "lines")
            .attr("stroke", (d, i) => {
                return color(d.name);
            })
            .attr("stroke-width", 1.5)
            .style("fill", "none");

        this.lineGraph.append("text")
            .attr('id', 'focusText')
            .attr("transform", () => {
                return "translate(2," + (this._margin_viewer.top - 3) + ")"
            })
            .style("font-size", () => {
                return "11px"
            })
            .style("visibility", "hidden");


        let bisectDate = d3.bisector((d) => {
            return d;
        }).left;

        let lineGraph = this.lineGraph;
        this.graphCanvasFront
            .append("rect")
            .attr("id", "mainrect")
            .attr('width', this._size.width - this.x_clip_margin)
            .attr('height', this.data_viewer_height)
            .attr("transform", "translate(" + 0 + "," + 1 + ")")
            //.attr("clip-path", "url(#dataCanvasClip)")
            .style("fill-opacity", "0.0")
            .on("mouseover", () => {
                if (this.popup) {
                    //tooltip.style("visibility", "visible");
                }
                lineGraph.selectAll("#focusCircle").style("visibility", "visible");
                lineGraph.selectAll("#focusText").style("visibility", "visible");
            })
            .on("mouseout", function () {
                //tooltip.style("visibility", "hidden");
                lineGraph.selectAll("#focusCircle").style("visibility", "hidden");
                lineGraph.selectAll("#focusText").style("visibility", "hidden");
            })
            .on("mousemove", () => {

                // Get current mouse position.
                let mouse = d3.mouse($("#graphCanvas" + this._index)[0]);
                let pos = this.dataCanvasXscaleZoom.invert(mouse[0]);

                let bisectPos = bisectDate(xdata, pos);
                if (bisectPos > 0 && xdata.length - 1 >= bisectPos) {
                }
            })
            .call(this.zoom);
    }

}

export {Renderer};