/**
 * Basic wrapper class for *visualize* **project**.
 * This class uses MathModel's objects and this class is extremely specific
 * to certain project. Do not reuse this class. This is just wrapper class!
 *  
 * Written by Geunyeol Ryu
 * @ 2019.06.06
 */

  /**
  * Packages.
  */
import { Intervals, Interval, Point } from "../Core/Util/MathModel";
import * as d3 from 'd3';
import {margin, size, DataManager, ptype, pelem, plist, pair, point} from '../Core/Util/util';
import $ from "jquery";
import './visualize.scss';
import * as Popper from 'popper.js';
import { json } from "d3";
import { pushd } from "shelljs";

/**
 * This is prop class
 */
class PropValue{

    /**
     * 
     * @param _value the actual value of proposition, true or false.
     * @param _extent the extent of proposition value.
     */
    constructor(
        private _value:string="",
        private _extent:[number, number]
        ){}

    get value():string{
        return this._value;
    }

    set value(value: string){
        this._value = value;
    }

    get extent():[number, number]{
        return this._extent;
    }
}

class Prop{
    private _prop_value:PropValue[] = []

    constructor(
        private _name:string="",
    ){}

    get name():string{
        return this._name;
    }

    set name(name:string){
        this._name = name;
    }

    push(value:string, extent:[number, number]){
        this._prop_value.push(new PropValue(value, extent))
    }

    get elems(){
        return this._prop_value;
    }

    includes(num:number):(string | undefined) {
        for(let el of this._prop_value){
            if(el.extent.includes(num)){
                return el.value;
            }
        }
        return undefined;
    }

    removeAll(){
        this._prop_value = [];
    }
}

class Props{
    private _props: Prop[] = []

    push(prop:Prop){
        this._props.push(prop);
    }

    removeAll(){
        this._props=[];
    }

    get elems(){
        return this._props;
    }
}

 /**
  * Json:
  * * Wrapper class for visualize project
  */
class Json {

    /**
     * Internally has intervals.
     */
    private _intervals: Intervals = new Intervals("data");
    public _props:Props = new Props();
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
        this._props.removeAll();
        // https://dmitripavlutin.com/how-to-iterate-easily-over-object-properties-in-javascript/
        // need to take both key and value.
        for(let [key1, value1] of Object.entries(this._jsonString)){
            if(key1=="data"){
                for(let i=0; i<value1.length;i++){
                    let obj = value1[i];
                    for(let [key, value] of Object.entries(obj)){
                        let tmp_interval:Interval = new Interval(key, i);
                        for (let v of Object.values(value)){
                            tmp_interval.push(new Point(parseFloat(v[0]), parseFloat(v[1]), key));
                        }
                        this._intervals.push(tmp_interval);
                    }
                }
            }
            // for the 
            else{
                let intv_len = this._intervals.length
                let counter = 0
                let intv = this.intervalList();
                for(let [key2, value2] of Object.entries(value1)){
                    let tmp: Prop = new Prop(key2)
                    for(let v of value2){
                        if(counter != intv_len-1){
                            tmp.push(v, [intv[counter], intv[counter+1]])
                        }
                        counter++;
                    }
                    this._props.push(tmp)
                }
                console.log(this._props);
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

    extentList(){
        var tmp:[number, number][][] = [];
        for(let el of this._intervals.elems){
            let tmp2:[number, number][] = [];
            tmp2.push([el.xExtent[0],2]);
            tmp2.push([el.xExtent[1],2]);
            if(tmp.includes(tmp2)){

            }
            else{
                tmp.push(tmp2);
            }
        }
        return tmp;
    }

    intervalList(){
        var tmp: number[] = [];
        // assert that parse being called before this function.
        //this.parse();
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
    public json:Json;

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


    setdata(jd: string){
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
        var tmp:string[] = []
        for(let i=0; i<len; i++){
            tmp.push(i.toString());
        }
        var colorScale = d3.scaleOrdinal(d3.schemeSet3)
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



        let scaleX = 
            d3.scaleLinear()
                .domain(jdata.xRange())
                .range([this.axis_delta, this.viewer_width-this.axis_delta]);
        
        var newHeight = this.viewer_height-this._margin_viewer.top;
        let scaleY = 
            d3.scaleLinear()
                .domain(jdata.yRange())
                .range([this.viewer_height-2*this._margin_viewer.top, this._margin_viewer.top]);


        let x_axis = d3.axisBottom(scaleX);
        let x_axis_bottom = d3.axisBottom(scaleX);
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

        var zoom = ()=>{ console.log("sivalk?"); return d3.zoom().on("zoom", ()=>{
            console.log("fuck");
        })}

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
        
    

        var lineGraph = g_viewer
            .attr("clip-path", "url(#clip)")
            .selectAll(".linegraph")
            .append("g")
            .attr("class", "linegraph")
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
            .attr("stroke", (d, i)=>{return colorScale(i.toString())})
            .attr("fill", "none")
            .attr("stroke-width", 1)
            .attr("transform", () => { return "translate(0,"+this._margin_viewer.top+")"})
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
            .attr("stroke", (d, i2)=>{return colorScale(i2.toString())})
            //.style("stroke", "black")
            .style("fill", "none")
            .style("stroke-width", "1px")
            .attr('id', 'focusCircle')
            .attr("transform", () => { return "translate(0,"+this._margin_viewer.top+")"})
            //.style("opacity", "0");
            
            //.attr('id', 'focusCircle')
            //.attr('r', 3)
            //.attr('class', 'circle focusCircle');
        var cx1 = this.json.dataByNameList("constx1");

          
        var bisectDate = d3.bisector(function(d:[number, number]) { return d[0]; }).left;
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
                var mouse = d3.mouse($(this._tag)[0]);
                var pos = scaleX.invert(mouse[0]);
                var i = bisectDate(cx1,pos);
                //console.log(pos);
                if (i <= 0 || cx1.length < i){
                    // below 0 is undefined
                }else{
                    
                    var d0:[number, number] = cx1[i - 1];
                    var d1:[number, number] = cx1[i];

                    
                    // work out which date value is closest to the mouse
                    var final_value:[number, number] = pos - d0[0] > d1[0] - pos ? d1 : d0;
                    var xx = scaleX(final_value[0]);
                    var yy = scaleY(final_value[1]);
                    
                    lineGraph.selectAll("#focusText")
                        .attr('x', xx)
                        .attr('y', (d,i2)=>{
                            var dd0:[number, number] = (jdataList[i2])[i-1];
                            var dd1:[number, number] = (jdataList[i2])[i];
                            //console.log(dd1)
                            var ffinal_value:[number, number] = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = scaleX(ffinal_value[0]);
                            var yyt = scaleY(ffinal_value[1]);
                            return yyt;    
                        })
                        .text((d, i2) => { 
                            var dd0:[number, number] = (jdataList[i2])[i-1];
                            var dd1:[number, number] = (jdataList[i2])[i];
                            //console.log(dd1)
                            var ffinal_value:[number, number] = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = scaleX(ffinal_value[0]);
                            var yyt = scaleY(ffinal_value[1]);    
                            return jdataName[i2]+"("+d3.format(".2f")(scaleX.invert(mouse[0]))+" , "+d3.format(".2f")(scaleY.invert(yyt))+")" 
                        })
                  /*  focus.select('#focusCircle')
                        .attr('cx', xx)
                        .attr('cy', yy)
                        .style("fill", rainbow(0.859))*/
                        lineGraph.selectAll("#focusCircle")
                        .attr('cx', xx)
                        .attr('cy', (d,i2)=>{
                            var dd0:[number, number] = (jdataList[i2])[i-1];
                            var dd1:[number, number] = (jdataList[i2])[i];
                            //console.log(dd1)
                            var ffinal_value:[number, number] = pos - dd0[0] > dd1[0] - pos ? dd1 : dd0;
                            var xxx = scaleX(ffinal_value[0]);
                            var yyt = scaleY(ffinal_value[1]);
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
            })


            const refEl = document.querySelector('#focusCircle');
            const popEl = document.querySelector('#focusText');
            console.log("hello")
            console.log(popEl);
            var popper = new Popper.default(refEl as Element, popEl as Element, {
                modifiers: {
                    flip: {
                          behavior: ['left', 'right', 'top','bottom']
                    }
                },

              });
              console.log(popper);
            
            
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
export { Json, Renderer };