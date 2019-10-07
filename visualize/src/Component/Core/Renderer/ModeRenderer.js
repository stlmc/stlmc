import * as d3 from 'd3';
import $ from "jquery";
import "./MainRenderer.scss";

class ModeRenderer {


    constructor(
        _size,
        _margin_viewer,
        _margin_controller,
        _index,
        _jd = '',
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
        this._index = _index;
        this._tag = "#mode"+this._index;
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

        this._selectedVariables = [];

    }

    /**
     * d3.select must be invoke after Reactjs's componentdidmount called.
     * This will get DOM elements well.
     */
    setCanvas(d) {
        // set main canvas
        this.canvas = d3.select(this._tag).append("svg").attr("id", "mode_svg")
            .attr("width", this._size.width).attr("height", this._size.height);
        //.attr("transform", "translate(0, "+ this._index * this.effective_controller_height_difference + ")");
        //this.canvas = d3.select(this._tag).append("svg").attr("id", "prop_svg"+this._index).attr("width", this._size.width).attr("height", this._size.height);
        //this.canvas = d3.select("#main_svg").append("g").attr("id", "prop"+this._index).attr("width", this._size.width).attr("height", 100);
        // set data canvas
        //this.setDataCanvas();
        this.setCanvasAxis();
        // set prop canvas
        this.setPropCanvas(d);
    }


    loadGraph(isEmpty, maxX, data, xrange, d) {
        this.dataXrange = maxX;
        this.xrange = xrange;
        console.log(xrange);
        this.setCanvas(d);
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
                .range([0, this.viewer_width]);


            this.dataCanvasXscaleZoom = this.dataCanvasXscale;

            // update when redraw, remove previous proposition graph.
            //this.propCanvas.selectAll("#propGraphGroup").remove();
            //this.propCanvas.selectAll("#focusCircle2").remove();


            this.propGraph = this.propCanvasBack
                .append("g")
                .attr("id", "modeGraph")
                .selectAll(".modeGraphData")
                .data(data)
                .enter();


            let scaleX = this.dataCanvasXscaleZoom ? this.dataCanvasXscaleZoom : this.dataCanvasXscale;
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
                .attr("class", "modeGraphData")
                .attr("stroke", "red")
                .attr("stroke-width", 1.5)
                // .attr("transform", () => {
                //     return "translate(0," + (this.viewer_height + this.effective_controller_height - this._margin_viewer.top +1.5) + ")"
                // });
        }

    }

    reload(isEmpty, propName, isRedraw) {
        this.isRedraw = isRedraw;
        //d3.selectAll("#main_svg").remove();
        //d3.selectAll("#tooltip").remove();
        if (!isEmpty) {
            this.setCanvas();
            this.updateProp(propName);
            this.draw();
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
            .range([0, this.viewer_width]);


        this.dataCanvasXscaleZoom = this.dataCanvasXscale;
    }



    /**
     * prop canvas has 2 cavases innerly, back prop canvas does nothing
     * and front prop canvas is for user interactions (such as, zooming, clipping, mouse moving etc)
     *
     * Need to use propCanvasFront for interactions and propCanvas(back) for data showing or redraw, update.
     */
    setPropCanvas(d) {

        // set prop canvas
        this.propCanvas = this.canvas.append("g").attr("width", this.controller_width).attr("height", this.effective_controller_height);
        // set clipping path

        this.propCanvas.append("clipPath")
            .attr("id", "propCanvasClip"+this._index)
            .append("rect")
            .attr("width", this.viewer_width - this.x_clip_margin)
            .attr("height", this.viewer_height + this.controller_height);
        //.attr("x", this.axis_delta + 1)
        //.attr("y", 3 * this._margin_viewer.top);

        // set canvas front
        this.propCanvasBack = this.propCanvas.append("g")
            .attr("id", "propCanvasBack"+this._index)
            //.attr("clip-path", "url(#dataCanvasClip)")
            .attr("clip-path", "url(#propCanvasClip)")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (this._margin_viewer.top - 20) + ")");

        // TODO: Add user interactions to propCanvas.
        this.propCanvasFront = this.propCanvas.append("g");

        // set scale function for y
        // 0: none, 1: false, 2: true, 3:none
        this.propCanvasYscale =
            d3.scaleLinear()
                .domain([0, 3])
                .range([this.effective_controller_height, 0]);

        let newHeight = this.viewer_height - this._margin_viewer.top;


        if(this._index == 0){
            // Add interval lines.
            this.propCanvasIntervalLines = this.propCanvasBack.append("g")
                .attr("id", "propCanvasIntervalLinesBase")
                .attr("transform", "translate(" + 0 + "," + (this.viewer_height - 30.0) + ")");
                //.attr("transform", "translate(" + 0 + "," + (newHeight + this.effective_controller_height_difference + 1) + ")");
            // tickValues is actual data line
            // e.g) if you put [1, 2] in the tickValues than, it will draw line to x:1 and x:2.
            this.propCanvasIntervalLines.call(d3.axisBottom(this.dataCanvasXscale).tickValues(this.xrange).tickSize((this.viewer_height + 100.0)).tickPadding(3).tickFormat(() => {
                return ""
            })).select(".domain").remove();
        } else {
            // Add interval lines.
            this.propCanvasIntervalLines = this.propCanvasBack.append("g")
                .attr("id", "propCanvasIntervalLines")
                .attr("transform", "translate(" + 0 + "," + (this.effective_controller_height - 30.0) + ")");
                //.attr("transform", "translate(" + 0 + "," + (newHeight + this.effective_controller_height_difference + 1) + ")");
            this.propCanvasIntervalLines.call(d3.axisBottom(this.dataCanvasXscale).tickValues(this.xrange).tickSize((this.viewer_height + 100.0)).tickPadding(3).tickFormat(() => {
                return ""
            })).select(".domain").remove();
        }


        // Add x axis for propCanvas.
        this.propCanvasXaxis = this.propCanvas.append("g")
            .attr("id", "propCanvasXaxis")
            .attr("transform", "translate(" + this.x_clip_margin + ", " + (newHeight) + ")")
            //.attr("transform", "translate(" + this.x_clip_margin + "," + (newHeight + (this.effective_controller_height_difference) + 1) + ")")
            .call(d3.axisBottom(this.dataCanvasXscale));

        // Add y axis.
        this.propCanvasYaxis = this.propCanvas.append("g")
            .attr("id", "propCanvasYaxis")
            .attr("transform", "translate(" + this.x_clip_margin + "," + (newHeight) + ")");
            //.attr("transform", "translate(" + this.x_clip_margin + "," + (newHeight + this.effective_controller_height_difference - this.effective_controller_height + 1) + ")");

        // todo
        this.propCanvasYaxis.call(d3.axisLeft(this.propCanvasYscale).ticks(4).tickFormat(
            (d) => {
                if (d === 1) {
                    return d.name + " = false"
                } else if (d === 2) {
                    return d.name + " = true"
                } else {
                    return " "
                }
            }));
    }

    drawPropCanvas() {

        // update when redraw, remove previous proposition graph.
        this.propCanvas.selectAll("#propGraphGroup").remove();
        this.propCanvas.selectAll("#focusCircle2").remove();


        this.propGraph = this.propCanvasBack
            .append("g")
            .attr("id", "propGraph")
            .selectAll(".propGraphData")
            .data([])
            .enter();


        let scaleX = this.dataCanvasXscaleZoom ? this.dataCanvasXscaleZoom : this.dataCanvasXscale;
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
            .attr("stroke-width", 1.5)
            .attr("transform", () => {
                return "translate(0," + (this.viewer_height + this.effective_controller_height - this._margin_viewer.top +1.5) + ")"
            });



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

    }

    setdata(jd) {
        if (!jd.isEmpty()) {
            this.json = jd;
            this._selectedVariables = this.json.variables;
        }

    }

    updateProp(propName) {
        this.propName = propName;
    }

    draw() {
        this.drawPropCanvas();
    }

}

export {ModeRenderer};