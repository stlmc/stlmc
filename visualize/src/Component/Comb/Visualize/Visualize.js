import * as d3 from 'd3';
import {Json} from '../../Visualize/Visualize';
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

    }


    setdata(jd){
        this.json = jd;
    }

    updatePopup(popup){
        this.popup = popup
    }

    getPropList(){
        return this.json.propNames;
    }

    draw(){

        // color
        // https://github.com/d3/d3-scale/blob/master/README.md#sequential-scales
        // https://bl.ocks.org/pstuffa/d5934843ee3a7d2cc8406de64e6e4ea5
        // https://github.com/d3/d3-scale-chromatic/blob/master/README.md
        


        var jdata = this.json.data;
        var jdataList = this.json.dataList();
        var newJdataList = this.json.getDataList();
        var jdataIntervalList = this.json.intervalList();
        var jdataName = jdata.names;
        console.log(jdataName)
        var jdataInter = this.json._props;

        var colorScale = d3.scaleOrdinal(d3.schemeCategory10)
        var propColor = d3.scaleLinear().domain([0,2])
        .range(["red", "blue"])

        var main = 
        d3.select(this._tag)
                .append("svg")
                .attr("width", this._size.width)
                .attr("height", this._size.height);
        
        var g_controller = 
                main.append("g")
                .attr("width", this.controller_width)
                .attr("heght", this.controller_height)

        var g_viewer = 
        main.append("g")
                .attr("class", "viewer")
                .attr("width", this.viewer_width)
                .attr("heght", this.viewer_height)

                var clip = g_viewer.append("clipPath")
.attr("id", "clip")
.append("rect")
.style("fill", "red")
.attr("width", this.viewer_width-2*this.axis_delta )
.attr("height", this.viewer_height-3*this._margin_viewer.top )
.attr("x", this.axis_delta+1)
.attr("y", 3*this._margin_viewer.top)

g_controller.append("clipPath")
.attr("id", "clip2")
.append("rect")
.style("fill", "red")
.attr("width", this.viewer_width-2*this.axis_delta )
.attr("height", this.viewer_height+this.controller_height )
.attr("x", this.axis_delta+1)
.attr("y", 3*this._margin_viewer.top)

var g_viewer2 = 
        main.append("g")
        .attr("clip-path", "url(#clip)");

        var g_controller2 = 
        main.append("g")
        .attr("clip-path", "url(#clip2)");

     
        var xrange = jdata.xRange();
        var yrange = jdata.yRange();

        let scaleX = 
            d3.scaleLinear()
                .domain([xrange[0], xrange[1] + 1])
                .range([this.axis_delta, this.viewer_width-this.axis_delta]);
        
        var newHeight = this.viewer_height-this._margin_viewer.top;
        let scaleY = 
            d3.scaleLinear()
                .domain([yrange[0] - 1, yrange[1] + 1])
                .range([this.viewer_height-2*this._margin_viewer.top, this._margin_viewer.top]);


        let scaleYBottom = 
            d3.scaleLinear()
                .domain([0, 3])
                .range([this.effective_controller_height, 0]);


        let x_axis = d3.axisBottom(scaleX);
        let y_axis = d3.axisLeft(scaleY);
        let y_axisBottom = d3.axisLeft(scaleYBottom);

        var make_y_grid = () => { return d3.axisBottom(scaleX); }
        var make_x_grid = () => { return d3.axisLeft(scaleY); }
        var make_interval_grid = () => {
            return d3.axisBottom(scaleX);
        }
     
        // Add the brush feature using the d3.brush function
        // initialize the brush area: start at 0,0 and finishes at width,height: it means I select the whole graph area
        let brush = 
        d3.brushX()                 
            .extent( [ 
                [this.axis_delta-1,newHeight+this.effective_controller_height_difference-this.effective_controller_height], 
                [this.viewer_width-this.axis_delta+1, newHeight + this.effective_controller_height_difference] 
            ]) 
            .on("start brush", ()=>{
               
            }) // Each time the brush selection changes, trigger the 'updateChart' function
            //.extent( [ [0,newHeight], [this.controller_width,this.effective_controller_height] ] )
            //.extent([[0, 0], [this._size.width_upper, this._size.height_upper]]);


        var xaxis_grid=g_viewer.append("g")
            .attr("id", "xaxis_grid")
            .attr("transform", "translate(0," +  newHeight + ")")
        //var ticks = scaleX.ticks();
        //ticks.push(scaleX(1.0))
        xaxis_grid.call(make_y_grid().tickSize(-(this.viewer_height-3*this._margin_viewer.top)).tickPadding(10).tickFormat(null))
  
        var xaxis=g_viewer.append("g")
            .attr("id", "xaxis")
            .attr("transform", "translate(0," +  newHeight + ")")
        
        xaxis.call(x_axis)
        //.tickFormat(null));
        var yaxis_grid = g_viewer.append("g")
            .attr("id", "yaxis_grid")
            .attr("transform", "translate(" +this.axis_delta+","+this._margin_viewer.top+")")
        yaxis_grid.call(make_x_grid().tickSizeInner(-(this.viewer_width-2*this.axis_delta)).tickPadding(10).tickFormat(null));

        var yaxis = g_viewer.append("g")
            .attr("id", "yaxis")
            .attr("transform", "translate(" +this.axis_delta+","+this._margin_viewer.top+")")
        yaxis.call(y_axis);

        var yaxis_bottom = g_controller.append("g")
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
           

        var xaxis_bottom2 = g_controller2.append("g")
        .attr("id", "xaxis_bottom")
        .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
        console.log(jdataIntervalList)
        xaxis_bottom2.call(d3.axisBottom(scaleX).tickValues(jdataIntervalList).tickSize(-(this.viewer_height+100)).tickPadding(3).tickFormat(()=>{ return "" })).select(".domain").remove();
        /*
        for (let el of jdataIntervalList){
            main.append("line")
                .attr("class", "zero")
                .attr("x1", scaleX(el))
                .attr("x2", scaleX(el))
                .attr("y1", scaleY(10))
                .attr("y2", scaleY((newHeight + this.effective_controller_height_difference+1)))
                .style("stroke", "black")
                //.attr("transform", "translate(0,"+(1)+")")
                .style("stroke-dasharray", "4");
            
        }*/

        /*
        var xaxis_bottom2_1 = g_controller
            .append("g")
            .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
            .call(d3.axisBottom(scaleX).tickFormat(
                (d, i)=>{
                    if (jdataIntervalList.includes(d)){
                        let v = jdataInter.elems[0].includes(d)
                        return v;
                    }
                    else{
                        return "";
                    }
                }
            ));*/
        
        var xaxis_bottom2_1 = g_controller
            .append("g")
            .attr('id', 'xaxis_bottom2_1')
            .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
            .call(d3.axisBottom(scaleX).tickFormat(
                ()=>{ 
                    return ""
                }));

            /*
        g_controller.append("defs").append("marker")
            .attr("id", "triangle-end")
            .attr("refX", 12)
            .attr("refY", 6)
            .attr("markerWidth", 30)
            .attr("markerHeight", 30)
            .attr("markerUnits","userSpaceOnUse")
            .attr("orient", "auto")
            .append("path")
            .attr("d", "M 0 0 12 6 0 12 3 6")
            //.attr("d", "M -6 0 6 6 -6 12 -3 6")
            .style("fill", "black");
        
            g_controller.append("defs").append("marker")
            .attr("id", "triangle-start")
            .attr("refX", 0)
            .attr("refY", 6)
            .attr("markerWidth", 30)
            .attr("markerHeight", 30)
            .attr("markerUnits","userSpaceOnUse")
            .attr("orient", "auto")
            .append("path")
            .attr("d", "M 0 6 12 0 9 6 12 12")
            .style("fill", "black");

        g_controller
            .append("g")
            .append("line")
            .attr("class", "zero")
            .attr("x1", scaleX(0))
            .attr("x2", scaleX(1))
            .attr("y1", scaleY(20))
            .attr("y2", scaleY(20))
            .style("stroke", "black")
            .attr("marker-end", "url(#triangle-end)")
            .attr("marker-start", "url(#triangle-start)")
            .attr("transform", "translate(0,"+(this.effective_controller_height+this.effective_controller_height_difference)+")")
            .style("stroke-dasharray", "4");*/
/*
        g_controller
            .append("g")
            .attr("transform", "translate(" +this.axis_delta+","+this._margin_viewer.top+")")
            .call(d3.axisLeft(scaleBandY))*/

        var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);



            var lineGenerator2 = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleYBottom(d[1]); }).curve(d3.curveMonotoneX);

        // https://visualize.tistory.com/331
        // Add a clipPath: everything out of this area won't be drawn.
        /*
        var clip = g_viewer.append("defs").append("SVG:clipPath")
        .attr("id", "clip")
        .append("SVG:rect")
        ///.attr("width", 100)
        .attr('width', this.viewer_width-2*this.axis_delta)
        .attr('height', this.viewer_height-2*this._margin_viewer.top+this.effective_controller_height)
        .attr("transform", "translate("+this.axis_delta+","+this._margin_viewer.top+")")
        .style("fill", "red")
        .style("fill-opacity", "0.5");
*/
var newX = scaleX;
var newY = scaleY;
var newBY = scaleYBottom;

                
        var lineGraph = g_viewer2
            .selectAll(".linegraph")
            .append("g")
            //.data(jdataList)
            .data(newJdataList)
            .enter()
            
            let drag = d3.drag()
            .on('start', ()=>{
                console.log("dragstart")
            })
            .on('drag', ()=>{
                console.log("dragging")
            })
            .on('end', ()=>{
                console.log("dragend")
            });

            var lineGraphColor = [];
            var lg = lineGraph.append("path")
            .attr("d", (d)=>{ 
                var res = ""
                for(let e of d.value){
                    res += lineGenerator(e)
                }
                return res
            })
            .attr("stroke", "blue")
            .attr("class", "liness")
            .attr("stroke", (d, i)=>{
                let c = colorScale((i+2).toString())
                lineGraphColor.push(c)
                return c
            })
            .attr("fill", "none")
            .attr("stroke-width", 1.5)
            .attr("transform", () => { return "translate(0,"+2*this._margin_viewer.top+")"})
            //.attr("class", "linegraph")
            
            console.log(this.json.extentList())
            var lineGraph2 = g_controller2
            .selectAll(".linegraph")
            .append("g")
            .data(this.json.extentList())
            .enter()
            
            lineGraph2.append("path")
            .attr("d", (d)=>{ 
                return lineGenerator2(d)
            })
            .attr("stroke", "blue")
            .attr("class", "liness2")
            .attr("stroke", (d, i)=>{return propColor((i+2).toString())})
            .attr("fill", "none")
            .attr("stroke-width", 1.5)
            .attr("transform", () => { return "translate(0,"+(this.viewer_height+2*this._margin_viewer.top-8.5)+")"})


        var focus = g_viewer
            //.append('g').style('display', 'none')
            .attr("transform", "translate(0,"+this._margin_viewer.top+")");

        lineGraph.append("text")
            .attr('id', 'focusText')
            .attr("transform", ()=> { return "translate(2,"+(this._margin_viewer.top-3)+")"})
            .style("font-size", ()=>{ return "11px" });

        var tooltip2 = d3.select(this._tag)
            .append("div")
              .style("position", "absolute")
              .style("visibility", "hidden")
              .style("background-color", "rgba(0, 0, 0, 0.7)")
              .style("border", "solid")
              .style("border-width", "1px")
              .style("border-radius", "5px")
              .style("padding", "10px")
              //.style("width", "300px")
              //.style("height", "300px")
              /*.html(`
              <p>I'm a tooltip written in HTML</p>
              <img src='https://github.com/holtzy/D3-graph-gallery/blob/master/img/section/ArcSmal.png?raw=true'></img>
              <br>Fancy<br>
              <span style='font-size: 40px;'>Isn't it?</span>`);*/

        
        // for caching.
        var lineGraph2x2 = [];
        var lineGraphText = [];
        /*
        lineGraph2.append("text")
            .attr('id', 'focusText2')
            .attr("transform", ()=> { return "translate(2,"+(this.viewer_height+2*this._margin_viewer.top)+")"})
            .text((d, i)=>{
                for(let el of d){          
                    if (jdataIntervalList.includes(el[0])){
                        let v = jdataInter.elems[0].includes(el[0])
                        lineGraphText.push(v)
                        return v;
                    }
                    else{
                        lineGraphText.push("")
                        return "";
                    }          
                }     
            })
            .attr("x", (d)=>{
                let min = d.reduce(
                    (acc, cur) => {
                        return acc[0] > cur[0]? cur:acc;
                    }
                )
                let max = d.reduce(
                    (acc, cur) => {
                        return acc[0] > cur[0]? acc:cur;
                    }
                )
                lineGraph2x2.push((min[0]+max[0])/2);
                return scaleX((min[0]+max[0])/2);
            })
            .attr("y", (d)=>{
                return scaleYBottom(2);
            })
            .style("font-size", ()=>{ return "11px" });
*/


        lineGraph2.append('circle')
            .attr("r", 7)
            .attr("stroke", (d, i2)=>{ return lineGraphColor[i2]})
            //.style("stroke", "black")
            .style("fill", "none")
            .style("stroke-width", "1px")
            .attr('id', 'focusCircle2')
            // newHeight + this.effective_controller_height_difference+1 is the maxium height of second axis bottom
            .attr("transform", () => { return "translate(0,"+(this.viewer_height+2*this._margin_viewer.top-8.5)+")"})
            .attr('cy', (d,i2)=>{
                var yyt = newBY(1);
                return yyt;    
            });

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
    newX = d3.event.transform.rescaleX(scaleX);
    newY = d3.event.transform.rescaleY(scaleY);
    //newBY = d3.event.transform.rescaleY(scaleYBottom);
    // update axes with these new boundaries
    xaxis.call(d3.axisBottom(newX))
    yaxis.call(d3.axisLeft(newY))
    //xaxis_bottom.call(d3.axisBottom(newX).tickValues(jdataIntervalList).tickSize(-(this.viewer_height)).tickPadding(10).tickFormat(null)).select(".domain").remove()
    xaxis_bottom2.call(d3.axisBottom(newX).tickValues(jdataIntervalList).tickSize(-(this.viewer_height+100)).tickPadding(10).tickFormat(null)).select(".domain").remove();
    
    /*
    xaxis_bottom2_1.call(d3.axisBottom(newX).tickFormat(
        (d, i)=>{
            if (jdataIntervalList.includes(d)){
                let v = jdataInter.elems[0].includes(d)
                return v;
            }
            else{
                return "";
            }
        }        
    ));*/

    xaxis_bottom2_1.call(d3.axisBottom(newX).tickFormat(()=>{ return "" }));



    /*
    lineGraph2.selectAll("#focusText2")
            .attr("x", (d, i2)=>{
                return newX(lineGraph2x2[i2]);
            })
*/

    var lineGenerator2 = 
    d3.line()
    //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
    .x(function(d) { return newX(d[0]); })
    .y(function(d) { return scaleYBottom(d[1]); }).curve(d3.curveMonotoneX);


    g_controller2
            .selectAll(".liness2")
            .attr("d", (d)=>{ return lineGenerator2(d)})

   

    var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return newX(d[0]); })
            .y(function(d) { return newY(d[1]); }).curve(d3.curveMonotoneX);
    // update circle position
    lineGraph
      .selectAll(".liness")
      .attr("d", (d) => {
        var res = ""
        for(let e of d.value){
            res += lineGenerator(e)
        }
        return res
      })
      //.attr('x', function(d) {return newX(d.Sepal_Length)})
      //.attr('y', function(d) {return newY(d.Petal_Length)});
  //Line_chart.select(".line").attr("d", line);
  //focus.select(".axis--x").call(xAxis);
  //context.select(".brush").call(brush.move, x.range().map(t.invertX, t));
  var mouse = d3.mouse($(this._tag)[0]);
  var pos = newX.invert(mouse[0]);
  var i = bisectDate(cx1,pos);

    if (cx1.length -1 < i){
        i = cx1.length -1;
    }    
    if(i === 0){
        i = 1;
    }
    console.log(cx1.length)
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
        lineGraph2.selectAll("#focusCircle2")
        .attr('cx', xx)
}
        );
    
        var bisectDate = d3.bisector(function(d) { return d[0]; }).left;

        g_controller
            .append("rect")
            .attr("id", "controllerRect")
            .attr("width", this.viewer_width-2*this.axis_delta)
            .attr('height', this.effective_controller_height)
            .attr("transform", "translate("+this.axis_delta+","+(this.viewer_height+2*this._margin_viewer.top-8.5)+")")
            .style("fill-opacity", "0.0")
            .on("mouseover")
           
        g_viewer
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
                var i = bisectDate(cx1,pos);
                //console.log(pos);
                if (i <= 0 || cx1.length -1 < i){
                    // below 0 is undefined
                    console.log("??!!")
                    
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
                                console.log("???");
                            }
                            return acc += (`
                                <li class="liclass">
                                    <div class="input-color">
                                        <input type="text" value="`+ cur + ` "/>
                                        <div class="color-box" style="background-color: `+lineGraphColor[i22]+`;"></div>
                                        <!-- Replace "#FF850A" to change the color -->
                                    </div>
                                </li>`);
                            //return acc += ('<p style="color:white")>' + cur + '</p>');
                        }, "")

                        newTString = ('<ul class=ulclass>' + newTString + '</ul>');

                        tooltip2.style("top", (200)+"px").style("left",(200)+"px").html(
                            newTString
                        )
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
                        });///.style('opacity', "1");
                    
                        lineGraph2.selectAll("#focusCircle2")
                        .attr('cx', xx)

                    
                    focus.select('#focusLineX')
                        .attr('x1', xx).attr('y1', scaleY(jdata.yRange()[0]))
                        .attr('x2', xx).attr('y2', scaleY(jdata.yRange()[1]))
                        //.style("stroke", rainbow(0.8))
                        .style("stroke-width",  "1px");
                    focus.select('#focusLineY')
                        .attr('x1', scaleX(jdata.xRange()[0])).attr('y1', yy)
                        .attr('x2', scaleX(jdata.xRange()[1])).attr('y2', yy)
                        //.style("stroke", rainbow(0.8))
                        .style("stroke-width",  "1px");
                    

                }
            }).call(
                zoom
            )

            
            
            /*.on("ondragstart",()=>{
                console.log("dragstart")
            }).on("ondrag",()=>{
                console.log("drag")
            }).on("ondragend", ()=>{
                console.log("dragend")
            })*/

            /*
            g_viewer.append("line")
            .attr("class", "zero")
            .attr("x1", scaleX(1))
            .attr("x2", scaleX(1))
            .attr("y1", scaleY(20))
            .attr("y2", scaleY(21))
            .style("stroke", "black")
            .attr("transform", "translate(0,"+this._margin_viewer.top+")")
            .style("stroke-dasharray", "4");*/
                //.attr("transform", "translate("+this._margin_controller.left+","+(this._margin_viewer.top+this._size.height_upper-this._size.height_lower+this._margin_controller.top)+")");
    }

    
}

export {Renderer};