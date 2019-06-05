import * as d3 from 'd3';
import {margin, size, DataManager, ptype, pelem, plist} from './util/util';
import $ from "jquery";

// 1회성 클래스라고 생각하자.
export class Line {
    public dataManager: DataManager = new DataManager();
    private viewer_width:number = 0.0;
    private viewer_height:number = 0.0;
    private controller_width:number = 0.0;
    private controller_height:number = 0.0;
    private height_delta:number = 100.0;
    private axis_delta:number = 50.0;
    private effective_controller_height_difference:number = 100;
    private effective_controller_height:number = 50;

    constructor(
        private _size: size,
        private _margin_viewer: margin, 
        private _margin_controller: margin, 
        private _tag: string = "#graph",
        private _jd: string = ''
        ){
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

    update(){

    }

    setdata(jd: string){
        this.dataManager.data = jd;
    }

    draw(){


        // color
        // https://github.com/d3/d3-scale/blob/master/README.md#sequential-scales
        var rainbow = d3.scaleSequential(d3.interpolateRainbow);

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
                .attr("heght", this.viewer_height);
                /*
              
                svg.append("rect")
                .attr("class", "outer")
                .attr("fill", "blue")
                .attr("width", 400)
                .attr("height", 300)
                .attr("transform", "translate("+this._margin_viewer.left+","+this._margin_viewer.top+")");
*/

        // g_controller.append("rect")
        // .attr("class", "outer")
        // .attr("fill", "yellow")
        // .attr("width", this.controller_width)
        // .attr("height", this._size.height_lower)

        // d3 min has type (number | undefined)
        // but domain has type number only
        // so you need explicit type casting
        // takes more than hour to know this...
        let x:pelem = this.dataManager.x[0][2].point_list as pelem;
        console.log(this.dataManager.x);
        /*
        for(let xx of this.dataManager.x){
            for(let yy of xx){
                //console.log(yy.point_list);
                x = yy.point_list as pelem;
            }
        }*/
        //x=x.map(function(el:number){return el*100;})
        //console.log(x);

        let y:pelem = this.dataManager.y[0][2].point_list as pelem;
        console.log(this.dataManager.y);
        /*
        for(let xx of this.dataManager.y){
            for(let yy of xx){
                //console.log(yy.point_list);
                y = yy.point_list as pelem;
            }
        }*/

        let d:ptype = this.dataManager.points[0][2].point_list;
        console.log(this.dataManager.points);
        // for(let xx of this.dataManager.points){
        //     //console.log(xx);
        //     for (let yy of xx){
        //         console.log(yy);
        //         d = yy.point_list;
        //     }
        // }
        let dd:[number, number][] = 
        [
            [1, 5],
            [20,20],
            [40,40], 
            [60,50],
            [80,5],  
            [100,60],
            [110, 80]
        ]

        /*
        let scaleX = 
            d3.scaleLinear()
                .domain([d3.min([1, 20, 40, 60, 80, 100, 110]) as number, d3.max([1, 20, 40, 60, 80, 100, 110]) as number])
                .range([this._margin_viewer.left, this._size.width_upper-this._margin_viewer.right]);
        let scaleY = 
            d3.scaleLinear()
                .domain([d3.min([5, 20, 40, 50, 5, 60, 80]) as number, d3.max([5, 20, 40, 50, 5, 60, 80]) as number])
                .range([this._size.height_upper-this._margin_viewer.bottom, this._margin_viewer.top]);*/

        let scaleX = 
            d3.scaleLinear()
                .domain([d3.min(x) as number, d3.max(x) as number])
                .range([this.axis_delta, this.viewer_width-this.axis_delta]);
        
        var newHeight = this.viewer_height-this._margin_viewer.top;
        let scaleY = 
            d3.scaleLinear()
                .domain([d3.min(y) as number, d3.max(y) as number])
                .range([this.viewer_height-2*this._margin_viewer.top, this._margin_viewer.top]);


        let x_axis = d3.axisBottom(scaleX);
        let x_axis_bottom = d3.axisBottom(scaleX);
        let y_axis = d3.axisLeft(scaleY);

        // Add the brush feature using the d3.brush function
        // initialize the brush area: start at 0,0 and finishes at width,height: it means I select the whole graph area
        let brush = 
        d3.brushX()                 
            .extent( [ 
                [this.axis_delta-1,newHeight+this.effective_controller_height_difference-this.effective_controller_height], 
                [this.viewer_width-this.axis_delta+1, newHeight + this.effective_controller_height_difference] 
            ]) 
            .on("start brush", this.update) // Each time the brush selection changes, trigger the 'updateChart' function
            //.extent( [ [0,newHeight], [this.controller_width,this.effective_controller_height] ] )
            //.extent([[0, 0], [this._size.width_upper, this._size.height_upper]]);

        
  
        g_viewer.append("g")
            .attr("transform", "translate(0," +  newHeight + ")")
            .call(x_axis);

        g_viewer.append("g")
            .attr("transform", "translate(" +this.axis_delta+","+this._margin_viewer.top+")")
            .call(y_axis);
        
        g_controller.append("g")
            .attr("transform", "translate(0," +  (newHeight + this.effective_controller_height_difference+1) + ")")
            .call(x_axis_bottom);
        
        
        g_controller
            .call( brush )

            
        var lineGenerator = 
            d3.line()
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);
        var areaGenerator = 
            d3.area()
            .x(function(d) { return scaleX(d[0]); })
            .y0(0)
            .y1(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);


        var areaGenerator2 = 
            d3.area()
            .x(function(d) { return scaleX(d[0]); })
            .y0(this.viewer_height-this._margin_viewer.top)
            .y1(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);
            console.log(d);
        var pathString = lineGenerator(d as plist) as string;
        var lineGraph = g_viewer.append("path")
            .attr("d", pathString)
            .attr("stroke", "blue")
            .attr("stroke-width", 1)
            .attr("transform", "translate(0,"+this._margin_viewer.top+")")

        // https://www.d3-graph-gallery.com/graph/area_basic.html
        // using basic area tutorial
        var areaString = areaGenerator(d as plist) as string;
        var areaString2 = areaGenerator2(d as plist) as string;
        /*
        g_viewer.append("path")
            .attr("d", areaString)
            .attr("fill-opacity", "0.0")
            .attr("transform", "translate(0,"+this._margin_viewer.top+")");
        g_viewer.append("path")
            .attr("d", areaString2)
            .attr("fill-opacity", "0.0")
            //.attr("transform", "translate(0,"+this._margin_viewer.top+")");*/
        /*
        lineGraph.append("path")
            .attr("class", "line")
            .attr("d", function(d) {
              return line(d.values);
            })
            .style("stroke", function(d) {
              return color(d.name);
            });
*/
        g_viewer.append("line")
            .attr("class", "zero")
            .attr("x1", scaleX(0.5))
            .attr("x2", scaleX(0.5))
            .attr("y1", scaleY(20.70))
            .attr("y2", scaleY(21))
            .style("stroke", rainbow(0.8))
            .attr("transform", "translate(0,"+this._margin_viewer.top+")")
            .style("stroke-dasharray", "4");
    /*
        g_viewer.append("rect")
            .attr("class", "outer")
            .attr("fill", "blue")
            .attr("width", this.viewer_width)
            .attr("height", 300)
            .attr("transform", "translate("+this._margin_viewer.left+","+this._margin_viewer.top+")");
*/
/*
        $(".outer").mousemove((e)=>{
            console.log("hello");
            console.log(scaleX.invert(e.pageX));
        });*/

        // focus tracking
        //http://bl.ocks.org/mikehadlow/93b471e569e31af07cd3

        var focus = g_viewer.append('g').style('display', 'none')
        .attr("transform", "translate(0,"+this._margin_viewer.top+")");
        focus.append("text")
            .attr('id', 'focusText')
            .attr("transform", "translate(2,-3)")
            .style("font-size", "11px");

        focus.append('line')
            .attr('id', 'focusLineX')
            .attr('class', 'focusLine');
        focus.append('line')
            .attr('id', 'focusLineY')
            .attr('class', 'focusLine');
        focus.append('circle')
            .attr('id', 'focusCircle')
            .attr('r', 3)
            .attr('class', 'circle focusCircle');


        var bisectDate = d3.bisector(function(d:[number, number]) { return d[0]; }).left;
        g_viewer
            .append("rect")
            .attr('width', this.viewer_width-2*this.axis_delta)
            .attr('height', this.viewer_height-2*this._margin_viewer.top)
            .attr("transform", "translate("+this.axis_delta+","+this._margin_viewer.top+")")
            .style("fill-opacity", "0.0")
            .on('mouseover', function() { focus.style('display', null); })
            .on('mouseout', function() { focus.style('display', 'none'); })
            .on("mousemove", ()=>{
                var mouse = d3.mouse($(this._tag)[0]);
                var pos = scaleX.invert(mouse[0]);
                var i = bisectDate(d as plist,pos);
                console.log(pos);
                if (i <= 0 || (d as plist).length <= i){
                    // below 0 is undefined
                }else{
                    var d0:[number, number] = (d as plist)[i - 1];
                    var d1:[number, number] = (d as plist)[i];

                    // work out which date value is closest to the mouse
                    var final_value:[number, number] = pos - d0[0] > d1[0] - pos ? d1 : d0;
                    var xx = scaleX(final_value[0]);
                    var yy = scaleY(final_value[1]);

                    focus.select("#focusText")
                        .attr('x', xx)
                        .attr('y', yy)
                        .text("("+d3.format(".2f")(scaleX.invert(mouse[0]))+" , "+d3.format(".2f")(scaleY.invert(mouse[1]))+")")
                    focus.select('#focusCircle')
                        .attr('cx', xx)
                        .attr('cy', yy)
                        .style("fill", rainbow(0.859))
                    focus.select('#focusLineX')
                        .attr('x1', xx).attr('y1', scaleY(d3.min(y) as number))
                        .attr('x2', xx).attr('y2', scaleY(d3.max(y) as number))
                        .style("stroke", rainbow(0.8))
                        .style("stroke-width",  "1px");
                    focus.select('#focusLineY')
                        .attr('x1', scaleX(d3.min(x) as number)).attr('y1', yy)
                        .attr('x2', scaleX(d3.max(x) as number)).attr('y2', yy)
                        .style("stroke", rainbow(0.8))
                        .style("stroke-width",  "1px");

                }
            })

                //.attr("transform", "translate("+this._margin_controller.left+","+(this._margin_viewer.top+this._size.height_upper-this._size.height_lower+this._margin_controller.top)+")");
    }
}