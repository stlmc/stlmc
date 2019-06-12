import * as d3 from 'd3';
import {Json} from '../../Visualize/Visualize';
import $ from "jquery";

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


    }


    setdata(jd){
        this.json = new Json(jd);
    }

    draw(){

        // color
        // https://github.com/d3/d3-scale/blob/master/README.md#sequential-scales
        // https://bl.ocks.org/pstuffa/d5934843ee3a7d2cc8406de64e6e4ea5
        // https://github.com/d3/d3-scale-chromatic/blob/master/README.md
        


        var jdata = this.json.data;
        var jdataList = this.json.dataList();
        var jdataIntervalList = this.json.intervalList();
        var jdataName = jdata.names;
        console.log(jdataName);

        var len = jdataList.length;
        var tmp = []
        for(let i=0; i<len; i++){
            tmp.push(i.toString());
        }
        var colorScale = d3.scaleOrdinal(d3.schemeCategory10)
        //.domain(tmp);

        console.log(jdataList)

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
.attr("x", this.axis_delta-1)
.attr("y", 3*this._margin_viewer.top)

var g_viewer2 = 
        main.append("g")
        .attr("clip-path", "url(#clip)");
     
        var xrange = jdata.xRange();
        var yrange = jdata.yRange();

        let scaleX = 
            d3.scaleLinear()
                .domain([xrange[0], xrange[1] + 1])
                .range([this.axis_delta, this.viewer_width-this.axis_delta]);

        let scaleXBottom = 
            d3.scaleLinear()
                .domain([xrange[0], xrange[1] + 1])
                .range([this.axis_delta, this.viewer_width-this.axis_delta]);
        
        var newHeight = this.viewer_height-this._margin_viewer.top;
        let scaleY = 
            d3.scaleLinear()
                .domain([yrange[0] - 1, yrange[1] + 1])
                .range([this.viewer_height-2*this._margin_viewer.top, this._margin_viewer.top]);


        let x_axis = d3.axisBottom(scaleX);
        let x_axis_bottom = d3.axisBottom(scaleXBottom);
        let y_axis = d3.axisLeft(scaleY);

        var make_y_grid = () => { return d3.axisBottom(scaleX); }
        var make_x_grid = () => { return d3.axisLeft(scaleY); }
     
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
        
        g_controller.append("g")
            .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
            .call(x_axis_bottom);
        
        
        g_controller
            .call( brush )
            .call( brush.move, scaleX.range());

        var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);

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


        var lineGraph = g_viewer2
            .selectAll(".linegraph")
            .append("g")
            .data(jdataList)
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

            var lg = lineGraph.append("path")
            .attr("d", (d)=>{ return lineGenerator(d)})
            .attr("stroke", "blue")
            .attr("class", "liness")
            .attr("stroke", (d, i)=>{return colorScale((i+2).toString())})
            .attr("fill", "none")
            .attr("stroke-width", 1.5)
            .attr("transform", () => { return "translate(0,"+2*this._margin_viewer.top+")"})
            //.attr("class", "linegraph")
 

        var focus = g_viewer
            //.append('g').style('display', 'none')
            .attr("transform", "translate(0,"+this._margin_viewer.top+")");

        lineGraph.append("text")
            .attr('id', 'focusText')
            .attr("transform", ()=> { return "translate(2,"+(this._margin_viewer.top-3)+")"})
            .style("font-size", ()=>{ return "11px" });

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
        var cx1 = this.json.dataByNameList("constx1");
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
    // update axes with these new boundaries
    xaxis.call(d3.axisBottom(newX))
    yaxis.call(d3.axisLeft(newY))

    var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return newX(d[0]); })
            .y(function(d) { return newY(d[1]); }).curve(d3.curveMonotoneX);
    // update circle position
    lineGraph
      .selectAll(".liness")
      .attr("d", (d) => { return lineGenerator(d) })
      //.attr('x', function(d) {return newX(d.Sepal_Length)})
      //.attr('y', function(d) {return newY(d.Petal_Length)});
  //Line_chart.select(".line").attr("d", line);
  //focus.select(".axis--x").call(xAxis);
  //context.select(".brush").call(brush.move, x.range().map(t.invertX, t));
  var mouse = d3.mouse($(this._tag)[0]);
  var pos = newX.invert(mouse[0]);
  var i = bisectDate(cx1,pos);
  if (i <= 0 || cx1.length < i){
    // below 0 is undefined
}else{
    if (cx1.length === i){
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
            return jdataName[i2]+"("+d3.format(".2f")(newX.invert(mouse[0]))+" , "+d3.format(".2f")(newY.invert(yyt))+"),"+this.json._prop[0]._name+"::"+this.json._prop[0]._value
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
}
        });
    
          
        var bisectDate = d3.bisector(function(d) { return d[0]; }).left;
        g_viewer
            .append("rect")
            .attr("id", "mainrect")
            .attr('width', this.viewer_width-2*this.axis_delta)
            .attr('height', this.viewer_height-2*this._margin_viewer.top)
            .attr("transform", "translate("+this.axis_delta+","+this._margin_viewer.top+")")
            //.style("fill", "red")
            .style("fill-opacity", "0.0")
            //.on('mouseover', function() { lineGraph.selectAll("#focusCircle").style('opacity', "1"); })
            //.on('mouseout', function() { lineGraph.selectAll("#focusCircle").style("opacity", "0");/*focus.style('display', 'none');*/ })
            .on("mousemove", ()=>{
                //var transform = d3.zoomTransform(this);
                //var xt = transform.rescaleX(scaleX), yt = transform.rescaleY(scaleY);
                var mouse = d3.mouse($(this._tag)[0]);
                var pos = newX.invert(mouse[0]);
                var i = bisectDate(cx1,pos);
                //console.log(pos);
                if (i <= 0 || cx1.length < i){
                    // below 0 is undefined
                    console.log(i)
                     
                }else{
                    
                    console.log("heh")
                    if (cx1.length === i){
                        i = cx1.length -1;
                    }    
                    if(i === 0){
                        i = 1;
                    }
                    var d0 = cx1[i - 1];
                    var d1 = cx1[i];
                    console.log(i)
                    console.log(d1)                    
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
                        });///.style('opacity', "1");

                    
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