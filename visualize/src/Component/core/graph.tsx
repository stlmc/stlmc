import * as d3 from 'd3';
import {margin, size, DataManager} from './util/util';

// 1회성 클래스라고 생각하자.
export class Line {
    constructor(
        private _margin_upper: margin = {top:20, right:10, bottom:50, left:10}, 
        private _margin_lower: margin = {top:20, right:10, bottom:10, left:10}, 
        private _size: size = {
            width_upper: 400,
            height_upper: 300,
            width_lower: 400,
            height_lower: 100
        },
        public data: DataManager = new DataManager(
            [
                [1, 5],
                [20,20],
                [40,40], 
                [60,50],
                [80,5],  
                [100,60],
                [110, 80]
            ]
        ),
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

    draw(){
        var svg = 
        d3.select(this._tag)
                .append("svg")
                .attr("width", 400)
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
        
        let scaleX = 
            d3.scaleLinear()
                .domain([d3.min(this.data.x) as number, d3.max(this.data.x) as number])
                .range([this._margin_upper.left, this._size.width_upper-this._margin_upper.right]);
        let scaleY = 
            d3.scaleLinear()
                .domain([d3.min(this.data.y) as number, d3.max(this.data.y) as number])
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
                .x((d) => { console.log(d[0]); return scaleX(d[0]); })
                .y((d) => { return scaleY(d[1]); }).curve(d3.curveMonotoneX);
            //.x(function(d) { console.log(d[0]); return margin.left+d[0]; })
            //.y(function(d) { return newHeight-d[1]; }).curve(d3.curveMonotoneX);
        var pathString = lineGenerator(this.data.data) as string;
        console.log(pathString);
         var lineGraph = svg.append("path")
      .attr("d", pathString)
      .attr("stroke", "blue")
      .attr("stroke-width", 1)
      .attr("fill", "none");
    }
}