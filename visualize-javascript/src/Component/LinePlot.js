import React, {Component} from 'react';
import * as d3 from "d3";
//https://bl.ocks.org/dimitardanailov/6f0a451d4457b9fa7bf6e0dddcd0f468
//https://bl.ocks.org/mbostock/3019563
//https://bl.ocks.org/d3indepth/e312c205b6b07757551bffafb265589b
//https://bl.ocks.org/gordlea/27370d1eea8464b04538e6d8ced39e89
//https://www.tutorialsteacher.com/d3js/axes-in-d3


class BarChart extends Component {
  constructor(props){
    super(props);
    this.getData = this.getData.bind(this);
    this.drawChart = this.drawChart.bind(this);
    this.preprocess = this.preprocess.bind(this);
    this.scaleX = this.scaleX.bind(this);
    this.scaleY = this.scaleY.bind(this);
    this.dataFunctionX = this.dataFunctionX.bind(this);
    this.dataFunctionY = this.dataFunctionY.bind(this);
    this.state = {
      margin: {top: 20, right: 10, bottom: 20, left: 10},
      data:  [ 
        [1, 5],  
        [20, 20],
        [40, 10], 
        [60,40],
        [80,5],  
        [100,60],
        [110,80]
      ],
      size:{
        width: 0, 
        height: 0
      },
      // Create scale
      scale:{},
      axis:{}
    }
  }
  componentDidMount() {
    this.setState(
      {
        size:{
        width: 400-this.state.margin.left-this.state.margin.right,
        height: 300 - this.state.margin.top - this.state.margin.bottom
        },
        axis:{
          x: d3.axisBottom().scale(this.state.scale.x),
          y: d3.axisLeft().scale(this.state.scale.y)
        }
      }
    )

    this.svg = d3.select("body")
    .append("svg")
    .attr("width", 400)
    .attr("height", 300)
    .append("g")
    .attr("transform", "translate("+ this.state.margin.left+","+this.state.margin.top+")");

    var newHeight = this.state.size.height-this.state.margin.bottom;
    //Append group and insert axis
   
    this.svg.append("g")
      .attr("transform", "translate(0," +  newHeight + ")")
       .call(this.state.axis.x);

       this.svg.append("g")
       .attr("transform", "translate(" +this.state.margin.left+",0)")
        .call(this.state.axis.y);
    this.drawChart();
  }

  scaleX(){
    return d3.scaleLinear()
          .domain([d3.min(this.preprocess(this.state.data, true)), d3.max(this.preprocess(this.state.data,true))])
          .range([this.state.margin.left, this.state.size.width-this.state.margin.right]);
  }
  scaleY(){
    return  d3.scaleLinear()
    .domain([d3.min(this.preprocess(this.state.data, false)), d3.max(this.preprocess(this.state.data, false))])
    .range([this.state.height-this.state.margin.bottom, this.state.margin.top]);
  }

  dataFunctionX(d){
      console.log(d[0]);
      return this.scaleX(d[0]);
  }

  dataFunctionY(d){
    return this.scaleY(d[1]);
  }
    
  getData(data, flag){
    var t = [];
    for (var el in data){
      if (flag){
        t.push(data[el].x);
      }
      else {
        t.push(data[el].y);
      }
    }
    return t;
  }

  preprocess(data, flag){
    var t = []
    for (var el in data){
      if(flag){
        t.push(data[el][0]);
      }
      else{
        t.push(data[el][1]);
      }
    }
    return t;
  }


  drawChart() {
    //var margin = {top: 20, right: 10, bottom: 20, left: 10};
  //The data for our line
  /*var lineData = [ 
    [1, 5],  
    [20, 20],
    [40, 10], 
    [60,40],
    [80,5],  
    [100,60],
    [110,80]
  ];
  var width = 400 - margin.left - margin.right,
        height = 300 - margin.top - margin.bottom;
*/
    
    // Append SVG 
   /* var svg = d3.select("body")
                .append("svg")
                .attr("width", 400)
                .attr("height", 300)
                .append("g")
                .attr("transform", "translate("+margin.left+","+margin.top+")");
*/




/*
                svg.append("rect")
                .attr("class", "outer")
                .attr("fill", "yellow")
                .attr("width", 400)
                .attr("height", 300);

                svg.append("rect")
                .attr("fill", "blue")
                .attr("width", width)
                .attr("height", height)
                .append("g")
                .attr("transform", "translate("+margin.left+","+margin.top+")");
*/
    // Create scale
    /*
    var scale = d3.scaleLinear()
                  .domain([d3.min(this.preprocess(lineData, true)), d3.max(this.preprocess(lineData,true))])
                  .range([margin.left, width-margin.right]);

    var scaleY = d3.scaleLinear()
                  .domain([d3.min(this.preprocess(lineData, false)), d3.max(this.preprocess(lineData, false))])
                  .range([height-margin.bottom, margin.top]);
    
    var y_axis = d3.axisLeft()
                  .scale(scaleY);

    // Add scales to axis
    var x_axis = d3.axisBottom()
                   .scale(scale);*/
console.log(this.svg);
/*
    var newHeight = this.state.height-this.state.margin.bottom;
    //Append group and insert axis
    this.svg.append("g")
      .attr("transform", "translate(0," +  newHeight + ")")
       .call(this.state.axis.x);

       this.svg.append("g")
       .attr("transform", "translate(" +this.state.margin.left+",0)")
        .call(this.state.axis.y);
*/
      /*
       var lineFunction = d3.line()
         .x(function(d) { return d.x; })
         .y(function(d) { return d.y; })
       // make line smooth.
         .curve(d3.curveMonotoneX);
*/
        var lineGenerator = d3.line()
            .x(this.dataFunctionX)
            .y(this.dataFunctionY).curve(d3.curveMonotoneX);
            //.x(function(d) { console.log(d[0]); return margin.left+d[0]; })
            //.y(function(d) { return newHeight-d[1]; }).curve(d3.curveMonotoneX);
        console.log(this.state.data);
        var pathString = lineGenerator(this.state.data);
        console.log(pathString);
         var lineGraph = this.svg.append("path")
      .attr("d", pathString)
      .attr("stroke", "blue")
      .attr("stroke-width", 1)
      .attr("fill", "none");

    // set the dimensions and margins of the graph
  //var margin = {top: 10, right: 30, bottom: 30, left: 60},
  //width = 460 ,//- margin.left - margin.right,
  //height = 400 - margin.top - margin.bottom;
  
  //var svg = d3.select('body').append('svg');
  //svg.attr('width', width);
  //svg.attr('height', height);
  // 5. X scale will use the index of our data
//var xScale = d3.scaleLinear()
//.domain([d3.min(this.getData(lineData, true)), d3.max(this.getData(lineData, true))]) // input
//.range([0, width]); // output

  // 3. Call the x axis in a group tag
//svg.append("g")
//.attr("class", "x axis")
//.attr("transform", "translate(0," + 0 + ")")
//.call(d3.axisBottom().scale(xScale)); // Create an axis component with d3.axisBottom

  //This is the accessor function we talked about above
  //var lineFunction = d3.line()
  //  .x(function(d) { return d.x; })
  //  .y(function(d) { return d.y; })
    // make line smooth.
  //  .curve(d3.curveMonotoneX);

    
  //The line SVG Path we draw
  //var lineGraph = svg.append("path")
  //  .attr("d", lineFunction(lineData))
  //  .attr("stroke", "blue")
  //  .attr("stroke-width", 1)
  //  .attr("fill", "none");


  }
        
  render(){
    return <div id="body">hihi</div>
  }
}
    
export default BarChart;
