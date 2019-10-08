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

    loadGraph(maxX, maxY, l, xdata, pdata, vardict) {
        console.log(xdata);
        this.refData = l;
        d3.select(this._tag).selectAll("#main_svg").remove();

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
            .attr("id", "graphCanvasXaxis" + this._index)
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this.data_viewer_height + 1) + ")")
            .call(d3.axisBottom(this.dataCanvasXscale));

        this.graphCanvasYaxis = this.canvas.append("g")
            .attr("id", "graphCanvasYaxis" + this._index)
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
                //this.propCanvasXaxis.call(d3.axisBottom(this.dataCanvasXscaleZoom));
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

                d3.selectAll(".modeLines")
                    .attr("d", (d) => {
                        return this.lineGenerator2(d);
                    });


                // Update lines positions.
                // Update position first and then rendering it
                this.lineGraph.selectAll(".lines")
                    .each((d) => {
                        d.newX = this.lineGenerator(d);
                    })

                this.lineGraph.selectAll(".lines")
                    .attr("d", (d) => {
                        return d.newX;
                    });


                // calculating mouse position
                let mouse = d3.mouse($("#graphCanvas" + this._index)[0]);
                let pos = this.dataCanvasXscaleZoom.invert(mouse[0]);
                let bisectDate = d3.bisector((d) => {
                    return d[0];
                }).left;
                let bisectData = bisectDate(this.refData, pos);

                if (this.refData.length - 1 < bisectData) {
                    bisectData = this.refData.length - 1;
                }
                if (bisectData === 0) {
                    bisectData = 1;
                }
                let d0 = this.refData[bisectData - 1];
                let d1 = this.refData[bisectData];

                // work out which date value is closest to the mouse
                let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                let x = this.dataCanvasXscaleZoom(final_data[0]);
                let y = this.dataCanvasYscaleZoom(final_data[1]);

                // Add focusing circle.
                this.lineGraph.selectAll("#focusCircle")
                    .attr('cx', x)
                    .attr('cy', (d, i) => {
                        let d0 = (l)[bisectData - 1];
                        let d1 = (l)[bisectData];
                        //console.log(dd1)
                        let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                        return this.dataCanvasYscaleZoom(final_data[1]);
                    });

            });
        console.log("rogogoggogogog");

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
            .selectAll(".linegraph")
            .append("g")
            .data(l)
            .enter();

        console.log(l);

        this.lineGraphColor = {};
        this.lineGraph.append("path")
            .attr("d", (d) => {
                return this.lineGenerator(d);
            })
            .attr("class", "lines")
            .attr("stroke", (d, i) => {
                let c = this.colorScale((i + 2).toString());
                this.lineGraphColor[d.name] = c;
                return c
            })
            .attr("transform", "translate(0, -20)")
            .attr("stroke-width", 1.5)
            .style("fill", "none");

        // TODO: Calculate initial circles positions.
        // this.lineGraph.append('circle')
        //     .attr("r", 7)
        //     .attr("stroke", (d, i) => {
        //         return this.lineGraphColor[d.name]
        //     })
        //     .style("stroke-width", "1px")
        //     .attr('id', 'focusCircle')
        //     .attr("transform", () => {
        //         return "translate(0, -20)"
        //     })
        //     .style("visibility", "hidden")
        //     .style("fill", "none");

        this.lineGraph.append("text")
            .attr('id', 'focusText')
            .attr("transform", () => {
                return "translate(2," + (this._margin_viewer.top - 3) + ")"
            })
            .style("font-size", () => {
                return "11px"
            })
            .style("visibility", "hidden");


        // Distinguish between original one and redrawn one because of graph coloring


        // TODO: Calculate initial circles positions.
        // this.lineGraph.append('circle')
        //     .attr("r", 7)
        //     .attr("stroke", (d, i) => {
        //         return this.lineGraphColor[d.name]
        //     })
        //     .style("stroke-width", "1px")
        //     .attr('id', 'focusCircle')
        //     .attr("transform", () => {
        //         return "translate(0, -20)"
        //     })
        //     .style("visibility", "hidden")
        //     .style("fill", "none");




        let bisectDate = d3.bisector((d) => {
            return d;
        }).left;

        let lineGraph = this.lineGraph;
        let mainrect = this.graphCanvasFront
            .append("rect")
            .attr("id", "mainrect")
            .attr('width', this._size.width - this.x_clip_margin)
            .attr('height', this.data_viewer_height)
            .attr("transform", "translate(" + this.x_clip_margin + "," + 1 + ")")
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
                console.log(l);
                let bisectPos = bisectDate(xdata, pos);
                if (bisectPos > 0 && xdata.length - 1 >= bisectPos) {
                    // Choose close one, between 2 of them.
                    let d0 = xdata[bisectPos - 1];
                    let d1 = xdata[bisectPos];

                    // work out which date value is closest to the mouse
                    let final_data = pos - d0 > d1 - pos ? d1 : d0;
                    let x = this.dataCanvasXscaleZoom(final_data);



                    let tmpText = [];
                    let tmpColor = [];
                    this.lineGraph.selectAll("#focusText")
                        //.attr('x', x)
                        // .attr('y', (d, i) => {
                        //     // Another d0, d1.
                        //     let d0 = (xdata)[bisectPos - 1];
                        //     let d1 = (xdata)[bisectPos];
                        //
                        //     let final_data = pos - d0 > d1 - pos ? d1 : d0;
                        //     return this.dataCanvasYscaleZoom(final_data);
                        // })
                        .text((d, i) => {
                            let d0 = (xdata)[bisectPos - 1];
                            let d1 = (xdata)[bisectPos];
                            //console.log(dd1)
                            let final_data = pos - d0 > d1 - pos ? d1 : d0;
                            //let newY = this.dataCanvasYscaleZoom(final_data);
                            let tstring = vardict.get(0) + "(" + d3.format(".2f")(this.dataCanvasXscaleZoom.invert(mouse[0])) + " , " + d3.format(".2f")(this.dataCanvasYscaleZoom.invert(mouse[1])) + ")";
                            if (!tmpText.includes(tstring)) {
                                tmpText.push(tstring);
                                tmpColor.push(d.name);
                            }
                            return tstring;
                        });


                    // this.lineGraph.selectAll("#focusCircle")
                    //     .attr('cx', x)
                    //     .attr('cy', (d, i) => {
                    //         console.log("???");
                    //         let d0 = (xdata)[bisectPos - 1];
                    //         let d1 = (xdata)[bisectPos];
                    //         let final_data = pos - d0 > d1 - pos ? d1 : d0;
                    //         return this.dataCanvasYscaleZoom(final_data);
                    //     });
                }
            })
            .call(this.zoom);
    }

}

export {Renderer};