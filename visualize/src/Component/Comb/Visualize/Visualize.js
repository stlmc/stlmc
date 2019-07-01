import * as d3 from 'd3';
import $ from "jquery";
import "./Visualize.scss";

class Renderer{


    constructor(
        _size,
        _margin_viewer, 
        _margin_controller, 
        _tag = "#graph",
        _jd = ''
        ){
        this.viewer_width = 0.0;
        this.viewer_height = 0.0;
        this.controller_width = 0.0;
        this.controller_height = 0.0;
        this.height_delta = 100.0;
        this.axis_delta = 50.0;
        this.effective_controller_height_difference = 100;
        this.effective_controller_height = 50;

        console.log("hey!")
        
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
        }
        
        this.viewer_width = this._size.width;
        this.viewer_height = this._size.height-this._margin_viewer.top-this._margin_viewer.bottom-this.height_delta;
        this.controller_width = this._size.width;
        this.controller_height = this._size.height-this._margin_controller.top-this._margin_controller.bottom-this.height_delta;
        this.popup = true;     

        this._selectedVariables = [];
    }

    /**
     * d3.select must be invoke after Reactjs's componentdidmount called.
     * This will get DOM elements well.
     */
    setCanvas(){
        // set main canvas
        this.canvas = d3.select(this._tag).append("svg").attr("id", "main_svg").attr("width", this._size.width).attr("height", this._size.height);   
        // set data canvas
        this.setDataCanvas();
        // set prop canvas
        this.setPropCanvas();
    }

    reload(isEmpty, propName){
        d3.selectAll("#main_svg").remove();
        d3.selectAll("#tooltip").remove();
        this.setCanvas();
        if(!isEmpty){
            this.updateProp(propName)
            this.draw();
        }
            
    }
    /**
     * data canvas has 2 cavases innerly, back data canvas does nothing
     * and front data canvas is for user interactions (such as, zooming, clipping, mouse moving etc)
     * 
     * Need to use dataCanvasFront for interactions and dataCanvas(back) for data showing or redraw, update.
     */
    setDataCanvas(){
        this.dataCanvas = this.canvas.append("g").attr("class", "viewer").attr("width", this.viewer_width).attr("heght", this.viewer_height)
        
        this.dataCanvas
            .append("clipPath")
            .attr("id", "dataCanvasClip")
                .append("rect")
                .style("fill", "red")
                .attr("width", this.viewer_width-2*this.axis_delta )
                .attr("height", this.viewer_height-3*this._margin_viewer.top )
                .attr("x", this.axis_delta+1)
                .attr("y", 3*this._margin_viewer.top)

        this.dataCanvasFront = 
                this.canvas.append("g")
                .attr("clip-path", "url(#dataCanvasClip)");
    }

    drawDataCanvas(){
        var jdata = this.json.data;
        var jdataList = this.json.dataList();
        //var newJdataList = this.json.getDataList();
        var newJdataList = this.json.getDataListMinor(this._selectedVariables);
        console.log(this._selectedVariables)
        console.log(this.json.names)
        console.log("newJdata: "+newJdataList)
        var jdataIntervalList = this.json.intervalList();
        var jdataName = jdata.names;

        var colorScale = d3.scaleOrdinal(d3.schemeCategory10)
        var yrange = jdata.yRange();
        
        var newHeight = this.viewer_height-this._margin_viewer.top;

        let scaleY = 
            d3.scaleLinear()
                .domain([yrange[0] - 1, yrange[1] + 1])
                .range([this.viewer_height-2*this._margin_viewer.top, this._margin_viewer.top]);




        let x_axis = d3.axisBottom(this.ScaleX);
        let y_axis = d3.axisLeft(scaleY);
        //let y_axisBottom = d3.axisLeft(scaleYBottom);

        var make_y_grid = () => { return d3.axisBottom(this.ScaleX); }
        var make_x_grid = () => { return d3.axisLeft(scaleY); }

        var xaxis_grid=this.dataCanvas.append("g")
            .attr("id", "xaxis_grid")
            .attr("transform", "translate(0," +  newHeight + ")")
        xaxis_grid.call(make_y_grid().tickSize(-(this.viewer_height-3*this._margin_viewer.top)).tickPadding(10).tickFormat(null))
  
        var xaxis=this.dataCanvas.append("g")
            .attr("id", "xaxis")
            .attr("transform", "translate(0," +  newHeight + ")")        
        xaxis.call(x_axis)

        var yaxis_grid = this.dataCanvas.append("g")
            .attr("id", "yaxis_grid")
            .attr("transform", "translate(" +this.axis_delta+","+this._margin_viewer.top+")")
        yaxis_grid.call(make_x_grid().tickSizeInner(-(this.viewer_width-2*this.axis_delta)).tickPadding(10).tickFormat(null));

        var yaxis = this.dataCanvas.append("g")
            .attr("id", "yaxis")
            .attr("transform", "translate(" +this.axis_delta+","+this._margin_viewer.top+")")
        yaxis.call(y_axis);

        /*
        var yaxis_bottom = this.propCanvas.append("g")
            .attr("id", "yaxis_bottom")
            .attr("transform", "translate(" +this.axis_delta+","+(newHeight + this.effective_controller_height_difference - this.effective_controller_height+1)+")")
            yaxis_bottom.call(y_axisBottom.ticks(4).tickFormat(
                (d)=>{
                    if (d==1){
                        return "false"
                    }
                    else if (d==2){
                        return "true"
                    }
                    else {
                        return " "
                    }
            }));
           */

        var xaxis_bottom2 = this.propCanvasFront.append("g")
        .attr("id", "xaxis_bottom")
        .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
        xaxis_bottom2.call(d3.axisBottom(this.ScaleX).tickValues(jdataIntervalList).tickSize(-(this.viewer_height+100)).tickPadding(3).tickFormat(()=>{ return "" })).select(".domain").remove();

        
        var xaxis_bottom2_1 = this.propCanvas
            .append("g")
            .attr('id', 'xaxis_bottom2_1')
            .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
            .call(d3.axisBottom(this.ScaleX).tickFormat(
                ()=>{ 
                    return ""
                }));

        let scaleX = this.ScaleX

        var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);


var newX = this.ScaleX;
var newY = scaleY;
//var newBY = scaleYBottom;

                
        var lineGraph = this.dataCanvasFront
            .selectAll(".linegraph")
            .append("g")
            //.data(jdataList)
            .data(newJdataList)
            .enter()

            this.lineGraphColor = [];
            var lg = lineGraph.append("path")
            .attr("d", (d)=>{ 
                if(this._selectedVariables.includes(d.name)){
                    var res = ""
                    for(let e of d.value){
                        res += lineGenerator(e)
                    }
                    return res
                }
            })
            .attr("stroke", "blue")
            .attr("class", "liness")
            .attr("stroke", (d, i)=>{
                let c = colorScale((i+2).toString())
                this.lineGraphColor.push(c)
                return c
            })
            .attr("fill", "none")
            .attr("stroke-width", 1.5)
            .attr("transform", () => { return "translate(0,"+2*this._margin_viewer.top+")"})

        var focus = this.dataCanvas
            //.append('g').style('display', 'none')
            .attr("transform", "translate(0,"+this._margin_viewer.top+")");

        lineGraph.append("text")
            .attr('id', 'focusText')
            .attr("transform", ()=> { return "translate(2,"+(this._margin_viewer.top-3)+")"})
            .style("font-size", ()=>{ return "11px" });

        var tooltip2 = d3.select(this._tag)
            .append("div")
              .attr("id", "tooltip")
              .style("position", "absolute")
              .style("visibility", "hidden")
              .style("background-color", "rgba(0, 0, 0, 0.7)")
              .style("border", "solid")
              .style("border-width", "1px")
              .style("border-radius", "5px")
              .style("padding", "10px")
 

            

        focus.append('line')
            .attr('id', 'focusLineX')
            .attr('class', 'focusLine');
        focus.append('line')
            .attr('id', 'focusLineY')
            .attr('class', 'focusLine');

            lineGraph.append('circle')
            .attr("r", 7)
            .attr("stroke", (d, i2)=>{return colorScale((i2+2).toString())})
            //.style("stroke", "black")
            .style("fill", "none")
            .style("stroke-width", "1px")
            .attr('id', 'focusCircle')
            .attr("transform", () => { return "translate(0,"+2*this._margin_viewer.top+")"})
            //.style("opacity", "0");
            
            //.attr('id', 'focusCircle')
            //.attr('r', 3)
            //.attr('class', 'circle focusCircle');
        
        var cx1 = this.json.dataByNameList(this.json.names[0]).flat();
        var zoom = d3.zoom()
        .scaleExtent([1, Infinity])
        //.translateExtent([[0, 0], [this.viewer_width, this.viewer_height]])
        .extent([[0, 0], [this.viewer_width, this.viewer_height]])
        .on("zoom", ()=>{
            // recover the new scale
    //var newX = d3.event.transform.rescaleX(scaleX);
    //var newY = d3.event.transform.rescaleY(scaleY);
    newX = d3.event.transform.rescaleX(this.ScaleX);
    this.newScaleX = newX;
    newY = d3.event.transform.rescaleY(scaleY);
    //newBY = d3.event.transform.rescaleY(scaleYBottom);
    // update axes with these new boundaries
    xaxis.call(d3.axisBottom(newX))
    yaxis.call(d3.axisLeft(newY))
    //xaxis_bottom.call(d3.axisBottom(newX).tickValues(jdataIntervalList).tickSize(-(this.viewer_height)).tickPadding(10).tickFormat(null)).select(".domain").remove()
    xaxis_bottom2.call(d3.axisBottom(newX).tickValues(jdataIntervalList).tickSize(-(this.viewer_height+100)).tickPadding(10).tickFormat(null)).select(".domain").remove();
    

    xaxis_bottom2_1.call(d3.axisBottom(newX).tickFormat(()=>{ return "" }));

    /*
    var lineGenerator2 = 
    d3.line()
    //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
    .x(function(d) { return newX(d[0]); })
    .y(function(d) { return scaleYBottom(d[1]); }).curve(d3.curveMonotoneX);
*/
    var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return newX(d[0]); })
            .y(function(d) { return newY(d[1]); }).curve(d3.curveMonotoneX);
    // update circle position
    lineGraph
      .selectAll(".liness")
      .attr("d", (d) => {
        if(this._selectedVariables.includes(d.name)){
        var res = ""
        for(let e of d.value){
            res += lineGenerator(e)
        }
        return res
      }
    })

  var mouse = d3.mouse($(this._tag)[0]);
  var pos = newX.invert(mouse[0]);
  this.pos = pos;
  var i = bisectDate(cx1,pos);

    if (cx1.length -1 < i){
        i = cx1.length -1;
    }    
    if(i === 0){
        i = 1;
    }
    var d0 = cx1[i - 1];
    var d1 = cx1[i];
    
    // work out which date value is closest to the mouse
    var final_value = pos - d0[0] > d1[0] - pos ? d1 : d0;
    var xx = newX(final_value[0]);
    var yy = newY(final_value[1]);
    
    lineGraph.selectAll("#focusText")
        .attr('x', xx)
        .attr('y', (d,i2)=>{
            var dd0 = (jdataList[i2])[i-1];
            var dd1 = (jdataList[i2])[i];
            //console.log(dd1)
            var ffinal_value = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
            var xxx = newX(ffinal_value[0]);
            var yyt = newY(ffinal_value[1]);
            return yyt;    
        })
        .text((d, i2) => { 
            var dd0 = (jdataList[i2])[i-1];
            var dd1 = (jdataList[i2])[i];
            //console.log(dd1)
            var ffinal_value = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
            var xxx = newX(ffinal_value[0]);
            var yyt = newY(ffinal_value[1]);    
            return jdataName[i2]+"("+d3.format(".2f")(newX.invert(mouse[0]))+" , "+d3.format(".2f")(newY.invert(yyt))+")"
        })
  /*  focus.select('#focusCircle')
        .attr('cx', xx)
        .attr('cy', yy)
        .style("fill", rainbow(0.859))*/
        lineGraph.selectAll("#focusCircle")
        .attr('cx', xx)
        .attr('cy', (d,i2)=>{
            var dd0 = (jdataList[i2])[i-1];
            var dd1 = (jdataList[i2])[i];
            //console.log(dd1)
            var ffinal_value = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
            var xxx = newX(ffinal_value[0]);
            var yyt = newY(ffinal_value[1]);
            return yyt;    
        });///.style('opacity', "1")
        //scaleX = newX;
        //scaleY = newY;
        this.propGraphGroup.selectAll("#focusCircle2")
        .attr('cx', xx)
    }
        );
    
        var bisectDate = d3.bisector(function(d) { return d[0]; }).left;

        this.propCanvas
            .append("rect")
            .attr("id", "controllerRect")
            .attr("width", this.viewer_width-2*this.axis_delta)
            .attr('height', this.effective_controller_height)
            .attr("transform", "translate("+this.axis_delta+","+(this.viewer_height+2*this._margin_viewer.top-8.5)+")")
            .style("fill-opacity", "0.0")
            //.on("mouseover")
           
        this.dataCanvas
            .append("rect")
            .attr("id", "mainrect")
            .attr('width', this.viewer_width-2*this.axis_delta)
            .attr('height', this.viewer_height-2*this._margin_viewer.top)
            .attr("transform", "translate("+this.axis_delta+","+this._margin_viewer.top+")")
            //.style("fill", "red")
            .style("fill-opacity", "0.0")
            .on("mouseover", ()=>{
                if (this.popup){
                    return tooltip2.style("visibility", "visible");
                }
            })
            .on("mouseout", function(){return tooltip2.style("visibility", "hidden");})
            //.on('mouseover', function() { lineGraph.selectAll("#focusCircle").style('opacity', "1"); })
            //.on('mouseout', function() { lineGraph.selectAll("#focusCircle").style("opacity", "0");/*focus.style('display', 'none');*/ })
            .on("mousemove", ()=>{
                //var transform = d3.zoomTransform(this);
                //var xt = transform.rescaleX(scaleX), yt = transform.rescaleY(scaleY);
                var mouse = d3.mouse($(this._tag)[0]);
                var pos = newX.invert(mouse[0]);
                this.pos = pos;
                var i = bisectDate(cx1,pos);
                //console.log(pos);
                if (i <= 0 || cx1.length -1 < i){
                    // below 0 is undefined
             
                    
                }else{
                    var d0 = cx1[i - 1];
                    var d1 = cx1[i];             
                    // work out which date value is closest to the mouse
                    var final_value = pos - d0[0] > d1[0] - pos ? d1 : d0;
                    var xx = newX(final_value[0]);
                    var yy = newY(final_value[1]);
                    
                    var tmpText = [];
                    lineGraph.selectAll("#focusText")
                        .attr('x', xx)
                        .attr('y', (d,i2)=>{
                            var dd0 = (jdataList[i2])[i-1];
                            var dd1 = (jdataList[i2])[i];
                            //console.log(dd1)
                            var ffinal_value = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = newX(ffinal_value[0]);
                            var yyt = newY(ffinal_value[1]);
                            return yyt;    
                        })
                        .text((d, i2) => { 
                            var dd0 = (jdataList[i2])[i-1];
                            var dd1 = (jdataList[i2])[i];
                            //console.log(dd1)
                            var ffinal_value = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = newX(ffinal_value[0]);
                            var yyt = newY(ffinal_value[1]);    
                            let tstring = jdataName[i2]+"("+d3.format(".2f")(newX.invert(mouse[0]))+" , "+d3.format(".2f")(newY.invert(yyt))+")" 
                            if(!tmpText.includes(tstring)){
                                tmpText.push(tstring);
                            }
                            return tstring;
                        })

                        // http://jsfiddle.net/VRyS2/1/
                        let newTString = tmpText.reduce((acc, cur, i22)=>{
                            if(acc == ""){
                               
                            }
                            return acc += (`
                                <li class="liclass">
                                    <div class="input-color">
                                        <input type="text" value="`+ cur + ` "/>
                                        <div class="color-box" style="background-color: `+this.lineGraphColor[i22]+`;"></div>
                                        <!-- Replace "#FF850A" to change the color -->
                                    </div>
                                </li>`);
                            //return acc += ('<p style="color:white")>' + cur + '</p>');
                        }, "")

                        newTString = ('<ul class=ulclass>' + newTString + '</ul>');

                        tooltip2.style("top", (200)+"px").style("left",(200)+"px").html(
                            newTString
                        )
                        lineGraph.selectAll("#focusCircle")
                        .attr('cx', xx)
                        .attr('cy', (d,i2)=>{
                            var dd0 = (jdataList[i2])[i-1];
                            var dd1 = (jdataList[i2])[i];
                            //console.log(dd1)
                            var ffinal_value = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = newX(ffinal_value[0]);
                            var yyt = newY(ffinal_value[1]);
                            return yyt;    
                        });///.style('opacity', "1");
                        this.xx = xx;
                        
                        this.propGraphGroup.selectAll("#focusCircle2")
                        .attr('cx', xx)
                        .attr('cy', (d,i2)=>{
                            var i222 = d3.bisect(d.xs,pos);
                            var yyt = this.propScaleY(d.ys[i222]);
                            return yyt;    
                        });    
                }
            }).call(
                zoom
            )
    }

    /**
     * Set base scale X for both data and proposition.
     * newScaleX for zooming and panning.
     */
    setBaseScale(){
        // get original data's x's extent since it is same as proposition's.
        let xrange = this.json.data.xRange();

        // set scale function for x
        this.ScaleX = 
            d3.scaleLinear()
            .domain([xrange[0], xrange[1] + 1])
            .range([this.axis_delta, this.viewer_width-this.axis_delta]);

        this.newScaleX = this.ScaleX;
    }

    /**
     * prop canvas has 2 cavases innerly, back prop canvas does nothing
     * and front prop canvas is for user interactions (such as, zooming, clipping, mouse moving etc)
     * 
     * Need to use propCanvasFront for interactions and propCanvas(back) for data showing or redraw, update.
     */
    setPropCanvas(){

        // set prop line color function
        this.propColor = d3.scaleLinear().domain([0,2]).range(["red", "blue"])
        // set prop canvas
        this.propCanvas = this.canvas.append("g").attr("width", this.controller_width).attr("heght", this.controller_height);
        // set clipping path
        this.propCanvas.append("clipPath")
            .attr("id", "propCanvasClip")
                .append("rect")
                .style("fill", "red")
                .attr("width", this.viewer_width-2*this.axis_delta )
                .attr("height", this.viewer_height+this.controller_height )
                .attr("x", this.axis_delta+1)
                .attr("y", 3*this._margin_viewer.top)
        // set canvas front
        this.propCanvasFront = 
            this.canvas.append("g")
            .attr("clip-path", "url(#propCanvasClip)");

        // set scale function for y
        // 0: none, 1: false, 2: true, 3:none
        this.propScaleY =
            d3.scaleLinear()
            .domain([0, 3])
            .range([this.effective_controller_height, 0]);
    }

    drawPropCanvas(){

        // update when redraw, remove previous proposition graph.
        this.propCanvasFront.selectAll("#propGraphGroup").remove();
        this.propCanvasFront.selectAll("#focusCircle2").remove();
        /**
         * this is proposition's graph group
         */
        let data = this.json.extentListByName(this.propName);
        //console.log(this.json.extentListByName(this.propName))
        this.propGraphGroup = this.propCanvasFront
            .append("g")
            .attr("id", "propGraphGroup")
            .selectAll(".propGraphData")
            .data([data])
            .enter()

    

        let propAxis = d3.axisLeft(this.propScaleY);
        let newHeight = this.viewer_height-this._margin_viewer.top;

        // add y axis
        var propAxisWithTick = this.propCanvas.append("g")
            .attr("id", "yaxis_bottom")
            .attr("transform", "translate(" +this.axis_delta+","+(newHeight + this.effective_controller_height_difference - this.effective_controller_height+1)+")")
        propAxisWithTick.call(propAxis.ticks(4).tickFormat(
                (d)=>{
                    if (d==1){
                        return "false"
                    }
                    else if (d==2){
                        return "true"
                    }
                    else {
                        return " "
                    }
            }));

        let scaleX = this.newScaleX;
        let scaleY = this.propScaleY;

        // set propostion graph line generator
        this.propLineGenerator = 
            d3.line()
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);

        /**
         * this is actual data of propsition graph
         */
        this.propGraphGroup
            .append("path")
            .attr("d", (d)=>{

                var res = ""
                for(let e of d.value){
                    res += this.propLineGenerator(e)
                }
                return res
            })
            .attr("class", "propGraphData")
            .attr("stroke", "red")
            .attr("fill", "none")
            .attr("stroke-width", 1.5)
            .attr("transform", () => { return "translate(0,"+(this.viewer_height+2*this._margin_viewer.top-8.5)+")"})

        /**
         * Draw circle
         */
        if(data.value.length != 0){
   
            let pos = this.pos;
            this.propGraphGroup
            .append('circle')
            .attr("r", 7)
            .attr("stroke", "red")
            //.style("stroke", "black")
            .style("fill", "none")
            .style("stroke-width", "1px")
            .attr('id', 'focusCircle2')
            // newHeight + this.effective_controller_height_difference+1 is the maxium height of second axis bottom
            .attr("transform", () => { return "translate(0,"+(this.viewer_height+2*this._margin_viewer.top-8.5)+")"})
            .attr('cx', this.xx)
            .attr('cy', (d,i2)=>{
                var i222 = d3.bisect(d.xs,pos);
                var yyt = this.propScaleY(d.ys[i222]);
                return yyt;    
            });
        }




        
    }

    redrawPropCanvas(propName){
        this.propName = propName;
        this.drawPropCanvas();
    }

    resetdata(jd){
        this.json = jd;
        if (!this.json.isEmpty()){
            this.setBaseScale();
        }
    }

    setdata(jd){
        this.json = jd;
        this._selectedVariables = this.json.names
        if (!this.json.isEmpty()){
            this.setBaseScale();
        }
    }

    updatePopup(popup){
        this.popup = popup;
    }

    updateProp(propName){
        this.propName = propName;
    }

    getPropList(){
        return this.json.propNames;
    }

    get selectedVariables(){
        return this._selectedVariables;
    }

    set selectedVariables(selected){
        if(selected){
            this._selectedVariables = [];
            for(let el of selected){
                console.log("selected: "+ el)
                this._selectedVariables.push(el)
            }
        }
    }


    draw(){

        // color
        // https://github.com/d3/d3-scale/blob/master/README.md#sequential-scales
        // https://bl.ocks.org/pstuffa/d5934843ee3a7d2cc8406de64e6e4ea5
        // https://github.com/d3/d3-scale-chromatic/blob/master/README.md
        this.drawDataCanvas();
        this.drawPropCanvas();
    }

    
}

export {Renderer};