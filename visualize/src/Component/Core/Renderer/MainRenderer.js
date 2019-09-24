import * as d3 from 'd3';
import $ from "jquery";
import "./MainRenderer.scss";

class Renderer {


    constructor(
        _size,
        _margin_viewer,
        _margin_controller,
        _tag = "#graph",
        _jd = ''
    ) {
        this.viewer_width = 0.0;
        this.viewer_height = 0.0;
        this.controller_width = 0.0;
        this.controller_height = 0.0;
        this.height_delta = 100.0;
        this.axis_delta = 50.0;
        this.x_clip_margin = 50.0;
        this.effective_controller_height_difference = 100;
        this.effective_controller_height = 50;

        console.log("hey!");

        this._size = _size;
        this._margin_viewer = _margin_viewer;
        this._margin_controller = _margin_controller;
        this._tag = _tag;
        this._jd = _jd;
        this._size = {
            width: this._size.width,
            height: this._size.height,
            width_upper: this._size.width_upper - this._margin_viewer.left - this._margin_viewer.right,
            height_upper: this._size.height_upper - this._margin_viewer.top - this._margin_viewer.bottom,
            width_lower: this._size.width_lower - this._margin_controller.left - this._margin_controller.right,
            height_lower: this._size.height_lower - this._margin_controller.top - this._margin_controller.bottom
        };

        this.viewer_width = this._size.width;
        this.viewer_height = this._size.height - this._margin_viewer.top - this._margin_viewer.bottom - this.height_delta;
        this.controller_width = this._size.width;
        this.controller_height = this._size.height - this._margin_controller.top - this._margin_controller.bottom - this.height_delta;
        this.popup = true;

        this._selectedVariables = [];
        this.isRedraw = false;
    }

    get selectedVariables() {
        return this._selectedVariables;
    }

    set selectedVariables(selected) {
        if (selected) {
            this._selectedVariables = [];
            for (let el of selected) {
                console.log("selected: " + el);
                this._selectedVariables.push(el);
            }
        }
    }

    /**
     * d3.select must be invoke after Reactjs's componentdidmount called.
     * This will get DOM elements well.
     */
    setCanvas() {
        this.loadDataset();
        // set main canvas
        this.canvas = d3.select(this._tag).append("svg").attr("id", "main_svg").attr("width", this._size.width).attr("height", this._size.height);

        let fps = d3.select("#graph span");

        let t0 = Date.now(), t1;

        d3.timer( function() {

            t1 = Date.now();
            fps.text( Math.round(1000 / (t1-t0)) + " fps");
            t0 = t1;

        });

        // set data canvas
        this.setDataCanvas();
    }

    resize(child_index){
        d3.select("#main_svg").attr("height", this._size.height + this.effective_controller_height*child_index)
    }

    /**
     * [loadDataset()] will make some kind of cache for dataset.
     * [this.json] will return some data after complicate process.
     * Using this cache will make everything go faster.
     */
    loadDataset() {
        this.data = this.json.data;
        this.dataListWithVariables = this.json.getDataListMinor(this._selectedVariables);
        this.intervalList = this.json.intervalList();
        this.dataName = this.data.names;
        this.refData = this.json.dataByNameList(this.json.variables[0]).flat();
    }

    reload(isEmpty, propName, isRedraw) {
        this.isRedraw = isRedraw;
        d3.selectAll("#main_svg").remove();
        d3.selectAll("#tooltip").remove();
        if (!isEmpty) {
            this.setCanvas();
            this.updateProp(propName);
            this.draw();
        }

    }

    /**
     * data canvas has 2 canvases innerly, back and front.
     * back data canvas does nothing and front data canvas is for user interactions (such as, zooming, clipping, mouse moving etc)
     *
     * Need to use dataCanvasFront for interactions and dataCanvas(back) for data showing or redraw, update.
     * dataCanvas has left margin. In order to fit right(center), you need to subtract left margin size to original width.
     * So, effective width of dataCanvas will be "this.width_size - 2 * this.x_clip_margin"
     *
     * [setDataCanvas()] will set canvas and its x axis and y axis with respect to dataset.
     */
    setDataCanvas() {
        this.dataCanvas = this.canvas.append("g").attr("class", "viewer").attr("width", this.viewer_width).attr("height", this.viewer_height);

        // Translate y for 20 is fitting rectangle to data canvas's y axis.
        // 20 is x axis height.
        // Clipping path area is just the area.
        this.dataCanvas
            .append("clipPath")
            .attr("id", "dataCanvasClip")
            .append("rect")
            .style("fill", "red")
            .attr("width", this.viewer_width - this.x_clip_margin)
            .attr("height", this.viewer_height - 2 * this._margin_viewer.top - 20);

        // Need to make clipping path area fit the exact area you want to fit.
        this.dataCanvasBack = this.dataCanvas.append("g")
            .attr("id", "dataCanvasBack")
            .attr("clip-path", "url(#dataCanvasClip)")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this._margin_viewer.top + 20) + ")");

        this.dataCanvasFront =
            this.dataCanvas.append("g");

        // Color scale for line plot in dataCanvas.
        // This will automatically add colors to your lines.
        this.colorScale = d3.scaleOrdinal(d3.schemeCategory10);


        // Set x and y axis of dataCanvas.
        this.setDataCanvasAxis();

        // Add zoom function to dataCanvas
        this.zoom = d3.zoom()
            .extent([[0, 0], [this.viewer_width, this.viewer_height]])
            .scaleExtent([1, Infinity])
            .translateExtent([[0, -this.dataYrange[1]], [Infinity, Infinity]])
            .on("zoom", () => {

                // Update scale functions to zoomed ones.
                this.dataCanvasXscaleZoom = d3.event.transform.rescaleX(this.dataCanvasXscale);
                this.dataCanvasYscaleZoom = d3.event.transform.rescaleY(this.dataCanvasYscale);

                // Update axis.
                this.dataCanvasXaxis.call(d3.axisBottom(this.dataCanvasXscaleZoom));
                this.dataCanvasYaxis.call(d3.axisLeft(this.dataCanvasYscaleZoom));
                //this.propCanvasXaxis.call(d3.axisBottom(this.dataCanvasXscaleZoom));
                d3.selectAll("#propCanvasXaxis").call(d3.axisBottom(this.dataCanvasXscaleZoom));
                d3.selectAll("#propCanvasIntervalLinesBase").call(d3.axisBottom(this.dataCanvasXscaleZoom).tickValues(this.intervalList).tickSize(-(this.viewer_height + 100)).tickPadding(3).tickFormat(() => {
                    return ""
                })).select(".domain").remove();
                d3.selectAll("#propCanvasIntervalLines").call(d3.axisBottom(this.dataCanvasXscaleZoom).tickValues(this.intervalList).tickSize(-(this.effective_controller_height)).tickPadding(3).tickFormat(() => {
                    return ""
                })).select(".domain").remove();


                // Make new line scale functions using latest scale functions.
                this.lineGenerator = d3.line()
                    .x((d) => {
                        return this.dataCanvasXscaleZoom(d[0]);
                    })
                    .y((d) => {
                        return this.dataCanvasYscaleZoom(d[1]);
                    })
                    .curve(d3.curveMonotoneX);

                // Update lines positions.
                // Update position first and then rendering it
                this.lineGraph.selectAll(".lines")
                    .each((d) => {
                        let res = "";
                        for (let e of d.value) {
                            res += this.lineGenerator(e)
                        }
                        d.newX = res;
                    })

                this.lineGraph.selectAll(".lines")
                    .attr("d", (d) => {
                        return d.newX;
                    });


                let scaleX = this.dataCanvasXscaleZoom;
                let scaleY = d3.scaleLinear()
                    .domain([0, 3])
                    .range([this.effective_controller_height, 0]);

                // set proposition graph line generator
                let propLineGenerator = d3.line()
                    .x(function (d) {
                        return scaleX(d[0]);
                    })
                    .y(function (d) {
                        return scaleY(d[1]);
                    }).curve(d3.curveMonotoneX);

                d3.selectAll(".propGraphData")
                    .attr("d", (d) => {
                        let res = "";
                        for (let e of d.value) {
                            res += propLineGenerator(e)
                        }
                        return res
                    });


                let mouse = d3.mouse($("#dataCanvasBack")[0]);
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

                this.lineGraph.selectAll("#focusText")
                    .attr('x', x)
                    .attr('y', (d, i) => {
                        let d0 = (this.dataListWithVariables[i].value.flat())[bisectData - 1];
                        let d1 = (this.dataListWithVariables[i].value.flat())[bisectData];
                        let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                        return this.dataCanvasYscaleZoom(final_data[1]);
                    })
                    .text((d, i) => {
                        let d0 = (this.dataListWithVariables[i].value.flat())[bisectData - 1];
                        let d1 = (this.dataListWithVariables[i].value.flat())[bisectData];
                        var final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                        var newY = this.dataCanvasYscaleZoom(final_data[1]);
                        return this.dataName[i] + "(" + d3.format(".2f")(this.dataCanvasXscaleZoom.invert(mouse[0])) + " , " + d3.format(".2f")(this.dataCanvasYscaleZoom.invert(newY)) + ")"
                    });

                this.lineGraph.selectAll("#focusCircle")
                    .attr('cx', x)
                    .attr('cy', (d, i) => {
                        let d0 = (this.dataListWithVariables[i].value.flat())[bisectData - 1];
                        let d1 = (this.dataListWithVariables[i].value.flat())[bisectData];
                        //console.log(dd1)
                        let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                        return this.dataCanvasYscaleZoom(final_data[1]);
                    });
            });


    }

    /**
     * Setting axis for the dataCanvas needs.
     * */
    setDataCanvasAxis() {

        // TODO: Remove this line soon.
        let newHeight = this.viewer_height - this._margin_viewer.top;

        // Get original data's x's and y's extent.
        // Will slow loading since json.data.xRange() itself need lots of calculations.
        // Need to be removed soon.
        this.dataXrange = this.data.xRange();
        this.dataYrange = this.data.yRange();

        // Add scale error to make lines fit the view box.
        // TODO: Update formula for error. Divide by 10 is not optimal.
        let XscaleError = (this.dataXrange[1] - this.dataXrange[0]) / 10;
        let YscaleError = (this.dataYrange[1] - this.dataYrange[0]) / 10;

        // Set scale function for x.
        // Clipping margin does the correction of calculate length of x axis.
        // X axis is move this.x_clip_margin by below code.
        this.dataCanvasXscale = d3.scaleLinear()
            .domain([this.dataXrange[0], this.dataXrange[1] + XscaleError])
            .range([0, this.viewer_width]);

        // Set scale function for y.
        // This process will do the same thing as x.
        this.dataCanvasYscale = d3.scaleLinear()
            .domain([this.dataYrange[0] - YscaleError, this.dataYrange[1] + YscaleError])
            .range([this.viewer_height - 2 * this._margin_viewer.top, this._margin_viewer.top]);

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
        this.dataCanvasXaxisGrid = this.dataCanvasBack.append("g")
            .attr("id", "dataCanvasXaxisGrid")
            .attr("transform", "translate(" + 0 + "," + (newHeight - this._margin_viewer.top - 20) + ")");
        this.dataCanvasXaxisGrid.call(make_y_grid()
            .tickSize(-(this.viewer_height - 3 * this._margin_viewer.top))
            .tickPadding(10)
            .tickFormat(() => {
                return "";
            }))
            .select(".domain").remove();

        this.dataCanvasYaxisGrid = this.dataCanvasBack.append("g")
            .attr("id", "dataCanvasYaxisGrid")
            .attr("transform", "translate(" + 0 + "," + (this._margin_viewer.top - 40) + ")");
        this.dataCanvasYaxisGrid.call(make_x_grid()
            .tickSizeInner(-(this.viewer_width - this.axis_delta))
            .tickPadding(10)
            .tickFormat(() => {
                return "";
            }))
            .select(".domain").remove();

        // Add clipping path.
        // If you are adding clipping path without margin, your zero of your axis will get lost.
        // Add x and y axis to dataCanvas.
        this.dataCanvasXaxis = this.dataCanvas.append("g")
            .attr("id", "dataCanvasXaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + newHeight + ")");
        this.dataCanvasXaxis.call(d3.axisBottom(this.dataCanvasXscale));

        this.dataCanvasYaxis = this.dataCanvas.append("g")
            .attr("id", "dataCanvasYaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + this._margin_viewer.top + ")");
        this.dataCanvasYaxis.call(d3.axisLeft(this.dataCanvasYscale));

    }

    /**
     * Set tooltips for data canvas.
     *
     * Add tooltip box, circles, texts for selected data.
     * */
    setDataCanvasTooltip() {
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

        // TODO: Calculate initial circles positions.
        this.lineGraph.append('circle')
            .attr("r", 7)
            .attr("stroke", (d, i) => {
                return this.lineGraphColor[d.name]
            })
            .style("stroke-width", "1px")
            .attr('id', 'focusCircle')
            .attr("transform", ()=>{
                return "translate(0, -20)"
            })
            .style("visibility", "hidden")
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
    }

    // TODO: Remove setBaseScale() later...
    /**
     * Set base scale X for both data and proposition.
     * newScaleX for zooming and panning.
     */
    setBaseScale() {
        // get original data's x's extent since it is same as proposition's.
        let xrange = this.json.data.xRange();

        // set scale function for x
        this.ScaleX =
            d3.scaleLinear()
                .domain([xrange[0], xrange[1] + 1])
                .range([this.axis_delta, this.viewer_width - this.axis_delta]);

        this.newScaleX = this.ScaleX;
    }

    setdata(jd) {
        if (!jd.isEmpty()) {
            this.json = jd;
            this._selectedVariables = this.json.variables;
            this.setBaseScale();
        }

    }

    updatePopup(popup) {
        this.popup = popup;
    }

    updateProp(propName) {
        this.propName = propName;
    }


    drawDataCanvas() {

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
        this.lineGraph = this.dataCanvasBack
            .selectAll(".linegraph")
            .append("g")
            .data(this.dataListWithVariables)
            .enter();

        console.log(this.dataListWithVariables)

        // Distinguish between original one and redrawn one because of graph coloring
        if (!this.isRedraw) {
            this.lineGraphColor = {};
            this.lineGraph.append("path")
                .attr("d", (d) => {
                    let res = "";
                    for (let e of d.value) {
                        res += this.lineGenerator(e)
                    }
                    return res
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
        } else {
            this.lineGraph.append("path")
                .attr("d", (d) => {
                    let res = "";
                    for (let e of d.value) {
                        res += this.lineGenerator(e)
                    }
                    return res
                })
                .attr("class", "lines")
                .attr("stroke", (d, i) => {
                    return this.lineGraphColor[d.name];
                })
                .attr("transform", "translate(0, -20)")
                .attr("stroke-width", 1.5)
                .style("fill", "none");
        }

        // Set extra tooltips.
        // This function needs to be called after data is set.
        this.setDataCanvasTooltip();

        // Add rect to the dataCanvasFront.
        // [mainrect] will be used to interacting with users.
        // This rect is transparent but will be used for interactions.
        // Translate y for 20 is fitting rectangle to data canvas's y axis.
        // 20 is x axis height.
        let tooltip = this.tooltip;
        let refData = this.refData;
        let bisectDate = d3.bisector((d) => {
            return d[0];
        }).left;

        let lineGraph = this.lineGraph;
        let mainrect = this.dataCanvasFront
            .append("rect")
            .attr("id", "mainrect")
            .attr('width', this.viewer_width - this.x_clip_margin)
            .attr('height', this.viewer_height - 2 * this._margin_viewer.top - 20)
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this._margin_viewer.top + 20) + ")")
            //.attr("clip-path", "url(#dataCanvasClip)")
            .style("fill-opacity", "0.0")
            .on("mouseover", () => {
                if (this.popup) {
                    tooltip.style("visibility", "visible");
                }
                lineGraph.selectAll("#focusCircle").style("visibility", "visible");
                lineGraph.selectAll("#focusText").style("visibility", "visible");
            })
            .on("mouseout", function () {
                tooltip.style("visibility", "hidden");
                lineGraph.selectAll("#focusCircle").style("visibility", "hidden");
                lineGraph.selectAll("#focusText").style("visibility", "hidden");
            })
            .on("mousemove", () => {

                // Get current mouse position.
                let mouse = d3.mouse($("#dataCanvasBack")[0]);
                let pos = this.dataCanvasXscaleZoom.invert(mouse[0]);
                let bisectPos = bisectDate(refData, pos);
                if (bisectPos > 0 && refData.length - 1 >= bisectPos) {

                    // Choose close one, between 2 of them.
                    let d0 = refData[bisectPos - 1];
                    let d1 = refData[bisectPos];

                    // work out which date value is closest to the mouse
                    let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                    let x = this.dataCanvasXscaleZoom(final_data[0]);

                    let tmpText = [];
                    let tmpColor = [];
                    this.lineGraph.selectAll("#focusText")
                        .attr('x', x)
                        .attr('y', (d, i) => {
                            // Another d0, d1.
                            let d0 = (this.dataListWithVariables[i].value.flat())[bisectPos - 1];
                            let d1 = (this.dataListWithVariables[i].value.flat())[bisectPos];

                            let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                            return this.dataCanvasYscaleZoom(final_data[1]);
                        })
                        .text((d, i) => {
                            let d0 = (this.dataListWithVariables[i].value.flat())[bisectPos - 1];
                            let d1 = (this.dataListWithVariables[i].value.flat())[bisectPos];
                            //console.log(dd1)
                            let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                            let newY = this.dataCanvasYscaleZoom(final_data[1]);
                            let tstring = d.name + "(" + d3.format(".2f")(this.dataCanvasXscaleZoom.invert(mouse[0])) + " , " + d3.format(".2f")(this.dataCanvasYscaleZoom.invert(newY)) + ")";
                            if (!tmpText.includes(tstring)) {
                                tmpText.push(tstring);
                                tmpColor.push(d.name);
                            }
                            return tstring;
                        });


                    // http://jsfiddle.net/VRyS2/1/
                    let newTString = tmpText.reduce((acc, cur, i22) => {
                        //console.log(acc);
                        return acc += (`
                                <li class="liclass">
                                    <div class="input-color">
                                        <input type="text" value="` + cur + ` "/>
                                        <div class="color-box" style="background-color: ` + this.lineGraphColor[tmpColor[i22]] + `;"></div>
                                        <!-- Replace "#FF850A" to change the color -->
                                    </div>
                                </li>`);
                    }, "");

                    newTString = ('<ul class=ulclass>' + newTString + '</ul>');

                    this.tooltip.style("top", (200) + "px").style("left", (200) + "px").html(
                        newTString
                    );

                    this.lineGraph.selectAll("#focusCircle")
                        .attr('cx', x)
                        .attr('cy', (d, i) => {
                            let d0 = (this.dataListWithVariables[i].value.flat())[bisectPos - 1];
                            let d1 = (this.dataListWithVariables[i].value.flat())[bisectPos];
                            let final_data = pos - d0[0] > d1[0] - pos ? d1 : d0;
                            return this.dataCanvasYscaleZoom(final_data[1]);
                        });
                }
            })
            .call(this.zoom);


    }


    draw() {

        // color
        // https://github.com/d3/d3-scale/blob/master/README.md#sequential-scales
        // https://bl.ocks.org/pstuffa/d5934843ee3a7d2cc8406de64e6e4ea5
        // https://github.com/d3/d3-scale-chromatic/blob/master/README.md
        this.drawDataCanvas();
    }


}

export {Renderer};