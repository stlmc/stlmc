import { Intervals, Interval, Point } from "../Core/Util/MathModel";
import * as d3 from 'd3';
import {margin, size, DataManager, ptype, pelem, plist, pair, point} from '../Core/Util/util';
import $ from "jquery";
/**
 * Basic wrapper class for *visualize* **project**.
 * This class uses MathModel's objects and this class is extremely specific
 * to certain project. Do not reuse this class. This is just wrapper class!
 *  
 * Written by Geunyeol Ryu
 * @ 2019.06.06
 */

 /**
  * Json:
  * * Wrapper class for visualize project
  */
class Json {

    /**
     * Internally has intervals.
     */
    private _intervals: Intervals = new Intervals("data");

    /**
     * 
     * @param _jsonString String parsing by internal json parser to string.
     */
    constructor(
        private _jsonString:string = ""
    ){
        //...
    }

    get data(){
        if(this._intervals.isEmpty()){
            this.parse();
            return this._intervals;
        }
        return this._intervals;
    }

    /**
     * @params jsonString Simple string that looks like Json file.
     */
    set string(jsonString:string){
        this._jsonString = jsonString;
        this.parse();
    }

    /**
     * Parsing interanl jsonString to make object.
     */
    parse = () => {
        this._intervals.removeAll();
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let i=0; i<this._jsonString.length;i++){
            let obj = this._jsonString[i];
            for(let [key, value] of Object.entries(obj)){
                let tmp_interval:Interval = new Interval(key, i);
                for (let v of Object.values(value)){
                    tmp_interval.push(new Point(parseFloat(v[0]), parseFloat(v[1]), key));
                }
                this._intervals.push(tmp_interval);
                //this._p_elem.push({name:key, point_list: tmp_point_list});
            }
        }
    }

    /**
     * This will find every intervals that have id which are the same as searching parameter.
     * @params id Interval number.
     */
    dataById = (id:number):Interval[] => {
        return this._intervals.intervalById(id);
    }

    /**
     * Usually, this will be variables name.
     * @params name Interval name.
     */
    dataByName = (name:string):Interval[] => {
        return this._intervals.intervalByName(name);
    }

    /**
     * Usually, this will be variables name.
     * @params name Interval name.
     */
    dataByNameList(name:string):[number, number][]{
        let tmp: [number, number][][] = [];
        let interv:Interval[] = this._intervals.intervalByName(name);
        for(let elem of interv){
            if(name==elem.name){
                tmp.push(elem.list);
            }
        }
        return tmp.flat();
    }

    /**
     * Get data List item... update... later..
     */
    dataList():[number, number][][]{
        var tmp: [number, number][][] = [];
        for(let e of this._intervals.names){
            tmp.push(this.dataByNameList(e));
        }
        return tmp;
    }

    intervalList(){
        var tmp: number[] = [];
        this.parse();
        for(let e of this._intervals.names){
            let interv:Interval[] = this._intervals.intervalByName(e);
            for(let el of interv){
                var min = el.xMin;
                var max = el.xMax;
                if (tmp.includes(max)){

                }
                else if (tmp.includes(min)){

                }
                else{
                    if(min==max){
                        tmp.push(min);
                    }
                    else{
                        tmp.push(min);
                        tmp.push(max);
                    }
                }
            }
        }
        return tmp;
    }
}

class Renderer{

    private viewer_width:number = 0.0;
    private viewer_height:number = 0.0;
    private controller_width:number = 0.0;
    private controller_height:number = 0.0;
    private height_delta:number = 100.0;
    private axis_delta:number = 50.0;
    private effective_controller_height_difference:number = 100;
    private effective_controller_height:number = 50;
    private j:Json;

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
        this.j = new Json(jd);
    }

    draw(){

        // color
        // https://github.com/d3/d3-scale/blob/master/README.md#sequential-scales
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
        
        let cx1 = this.j.dataByName("constx1");
        let cx2 = this.j.dataByName("constx2");
        let x1 = this.j.dataByName("x1");
        let x2 = this.j.dataByName("x2");

        var ilist = this.j.intervalList();
        console.log(ilist);

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
                .domain(this.j.data.xExtent())
                .range([this.axis_delta, this.viewer_width-this.axis_delta]);
        
        var newHeight = this.viewer_height-this._margin_viewer.top;
        let scaleY = 
            d3.scaleLinear()
                .domain(this.j.data.yExtent())
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

        console.log(ilist);    
        var lineGenerator = 
            d3.line()
            //.defined(function(d, i, da){ console.log("hehe"); console.log(d[0]); var r= !ilist.includes(d[0]); console.log(r); return r;})
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);

        
        var lineGraph = g_viewer
            .selectAll(".linegraph")
            .append("g")
            .attr("class", "linegraph")
            .data(this.j.dataList())
            .enter()
            

            lineGraph.append("path")
            .attr("d", (d)=>{ return lineGenerator(d)})
            .attr("stroke", "blue")
            //.attr("stroke", (d)=>{ return rainbow((d as [number, number][])[0][0]);  })
            .attr("fill", "none")
            .attr("stroke-width", 1)
            .attr("transform", () => { return "translate(0,"+this._margin_viewer.top+")"})
            //.attr("class", "linegraph")
            

 

        var focus = g_viewer
            //.append('g').style('display', 'none')
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

            lineGraph.append('circle')
            .attr("r", 7)
            .style("stroke", "black")
            .style("fill", "none")
            .style("stroke-width", "1px")
            .attr('id', 'focusCircle')
            .attr("transform", () => { return "translate(0,"+this._margin_viewer.top+")"})
            //.style("opacity", "0");
            
            //.attr('id', 'focusCircle')
            //.attr('r', 3)
            //.attr('class', 'circle focusCircle');
            var mainlist = this.j.dataList();

        var bisectDate = d3.bisector(function(d:[number, number]) { return d[0]; }).left;
        g_viewer
            .append("rect")
            .attr('width', this.viewer_width-2*this.axis_delta)
            .attr('height', this.viewer_height-2*this._margin_viewer.top)
            .attr("transform", "translate("+this.axis_delta+","+this._margin_viewer.top+")")
            .style("fill-opacity", "0.0")
            //.on('mouseover', function() { lineGraph.selectAll("#focusCircle").style('opacity', "1"); })
            //.on('mouseout', function() { lineGraph.selectAll("#focusCircle").style("opacity", "0");/*focus.style('display', 'none');*/ })
            .on("mousemove", ()=>{
                var mouse = d3.mouse($(this._tag)[0]);
                var pos = scaleX.invert(mouse[0]);
                var i = bisectDate(this.j.dataByNameList("constx1"),pos);
                console.log(pos);
                if (i <= 0 || this.j.dataByNameList("constx1").length < i){
                    // below 0 is undefined
                }else{
                    
                    var d0:[number, number] = (this.j.dataByNameList("constx1"))[i - 1];
                    var d1:[number, number] = (this.j.dataByNameList("constx1"))[i];

                    
                    // work out which date value is closest to the mouse
                    var final_value:[number, number] = pos - d0[0] > d1[0] - pos ? d1 : d0;
                    var xx = scaleX(final_value[0]);
                    var yy = scaleY(final_value[1]);
                    
                    focus.select("#focusText")
                        .attr('x', xx)
                        .attr('y', yy)
                        .text("("+d3.format(".2f")(scaleX.invert(mouse[0]))+" , "+d3.format(".2f")(scaleY.invert(mouse[1]))+")")
                  /*  focus.select('#focusCircle')
                        .attr('cx', xx)
                        .attr('cy', yy)
                        .style("fill", rainbow(0.859))*/
                        lineGraph.selectAll("#focusCircle")
                        .attr('cx', xx)
                        .attr('cy', (d,i2)=>{
                            var dd0:[number, number] = (this.j.dataList()[i2])[i-1];
                            var dd1:[number, number] = (this.j.dataList()[i2])[i];
                            //console.log(dd1)
                            var ffinal_value:[number, number] = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = scaleX(ffinal_value[0]);
                            var yyt = scaleY(ffinal_value[1]);
                            return yyt;    
                        });///.style('opacity', "1");

                    
                    focus.select('#focusLineX')
                        .attr('x1', xx).attr('y1', scaleY(this.j.data.yExtent()[0]))
                        .attr('x2', xx).attr('y2', scaleY(this.j.data.yExtent()[1]))
                        //.style("stroke", rainbow(0.8))
                        .style("stroke-width",  "1px");
                    focus.select('#focusLineY')
                        .attr('x1', scaleX(this.j.data.xExtent()[0])).attr('y1', yy)
                        .attr('x2', scaleX(this.j.data.xExtent()[1])).attr('y2', yy)
                        //.style("stroke", rainbow(0.8))
                        .style("stroke-width",  "1px");

                }
            })
            g_viewer.append("line")
            .attr("class", "zero")
            .attr("x1", scaleX(1))
            .attr("x2", scaleX(1))
            .attr("y1", scaleY(20))
            .attr("y2", scaleY(21))
            .style("stroke", "black")
            .attr("transform", "translate(0,"+this._margin_viewer.top+")")
            .style("stroke-dasharray", "4");
                //.attr("transform", "translate("+this._margin_controller.left+","+(this._margin_viewer.top+this._size.height_upper-this._size.height_lower+this._margin_controller.top)+")");
    }
}
export { Json, Renderer };