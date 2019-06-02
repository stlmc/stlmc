import * as d3 from 'd3';
import {margin, size, DataManager, ptype, pelem, plist} from './util/util';

// 1회성 클래스라고 생각하자.
export class Line {
    public dataManager: DataManager = new DataManager();
    constructor(
        private _jd: string = '',
        private _margin_upper: margin = {top:20, right:20, bottom:50, left:20}, 
        private _margin_lower: margin = {top:20, right:20, bottom:10, left:20}, 
        private _size: size = {
            width_upper: 420,
            height_upper: 300,
            width_lower: 420,
            height_lower: 100
        },
        private _tag: string = "#graph"){
        this._size = {
             width_upper: this._size.width_upper - this._margin_upper.left - this._margin_upper.right,
             height_upper: this._size.height_upper - this._margin_upper.top - this._margin_upper.bottom,
             width_lower: this._size.width_lower - this._margin_lower.left - this._margin_lower.right,
             height_lower: this._size.height_lower - this._margin_lower.top - this._margin_lower.bottom
        }
    }

    update(){

    }

    setdata(jd: string){
        this.dataManager.data = jd;
        //this.data.jsondata(jd);
    }

    draw(){
        //this.dataManager.data = this._jd;
        //console.log(this.dataManager.x);
        var svg = 
        d3.select(this._tag)
                .append("svg")
                .attr("width", 420)
                .attr("height", 300)
                .append("g")
                .attr("transform", "translate("+this._margin_upper.left+","+this._margin_upper.top+")");

                /*
              
                svg.append("rect")
                .attr("class", "outer")
                .attr("fill", "blue")
                .attr("width", 400)
                .attr("height", 300)
                .attr("transform", "translate("+this._margin_upper.left+","+this._margin_upper.top+")");
*/
                svg.append("rect")
                .attr("class", "outer")
                .attr("fill", "yellow")
                .attr("width", this._size.width_lower)
                .attr("height", this._size.height_lower)
                .attr("transform", "translate("+this._margin_lower.left+","+(this._margin_upper.top+this._size.height_upper-this._size.height_lower+this._margin_lower.top)+")");
        
            
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
                .range([this._margin_upper.left, this._size.width_upper-this._margin_upper.right]);
        let scaleY = 
            d3.scaleLinear()
                .domain([d3.min([5, 20, 40, 50, 5, 60, 80]) as number, d3.max([5, 20, 40, 50, 5, 60, 80]) as number])
                .range([this._size.height_upper-this._margin_upper.bottom, this._margin_upper.top]);*/

        let scaleX = 
            d3.scaleLinear()
                .domain([d3.min(x) as number, d3.max(x) as number])
                .range([this._margin_upper.left, this._size.width_upper-this._margin_upper.right]);
        let scaleY = 
            d3.scaleLinear()
                .domain([d3.min(y) as number, d3.max(y) as number])
                .range([this._size.height_upper-this._margin_upper.bottom, this._margin_upper.top]);

        let x_axis = d3.axisBottom(scaleX);
        let x_axis_bottom = d3.axisBottom(scaleX);
        let y_axis = d3.axisLeft(scaleY);

        // add brush
        let brush = d3.brush()
            .extent([[0, 0], [this._size.width_upper, this._size.height_upper]]);

        var newHeight = this._size.height_upper-this._margin_upper.bottom;
  
        svg.append("g")
            .attr("transform", "translate(0," +  newHeight + ")")
            .call(x_axis);

       svg.append("g")
            .attr("transform", "translate(" +this._margin_upper.left+",0)")
            .call(y_axis);
        
        svg.append("g")
            .attr("transform", "translate(0," +  (this._margin_upper.top+this._size.height_upper-this._size.height_lower+this._margin_lower.top+this._size.height_lower-this._margin_lower.bottom) + ")")
            .call(x_axis_bottom);
        
        svg
            .call( d3.brush()                 // Add the brush feature using the d3.brush function
            .extent( [ [0,0], [400,300] ] ) // initialise the brush area: start at 0,0 and finishes at width,height: it means I select the whole graph area
            .on("start brush", this.update) // Each time the brush selection changes, trigger the 'updateChart' function
            )


        var lineGenerator = 
            d3.line()
                //.x((d) => { console.log(d[0]); return scaleX(d[0]); })
                //.y((d) => { console.log(d[1]); return scaleY(d[1]); });//.curve(d3.curveMonotoneX);
            .x(function(d) { return scaleX(d[0]); })
            .y(function(d) { return scaleY(d[1]); }).curve(d3.curveMonotoneX);
            console.log(d);
        var pathString = lineGenerator(d as plist) as string;
        //console.log(pathString);
        var lineGraph = svg.append("path")
      .attr("d", pathString)
      .attr("stroke", "blue")
      .attr("stroke-width", 1)
      .attr("fill", "none");
    }
}