import React from 'react';
import logo from './logo.svg';
import './App.css';
import './stylesheets/main.scss';
import ReactApexChart from "react-apexcharts";
import BarChart from "./Component/LinePlot";
import { Link } from 'react-router-dom';
import { Switch, BrowserRouter as Router, Route } from 'react-router-dom';
import * as d3 from "d3";

function generateData(count, yrange) {
  var i = 0;
  var series = [];
  while (i < count) {
      var x = 't' + (i + 1).toString();
      var y = Math.floor(Math.random() * (yrange.max - yrange.min + 1)) + yrange.min;

      series.push({
          x: x,
          y: y
      });
      i++;
  }
  return series;
}


class App extends React.Component {
  constructor(props) {
    super(props);
    this.List = this.List.bind(this);
    this.state = {
      json: require('./ode_data/test.json'), 
      div:['0', '1', '2'],
      options: {
        dataLabels: {
          enabled: false
        },
        colors: ["#008FFB"],

        title: {
          text: 'HeatMap Chart For Proposition'
        }
      },
      series: [
        {
          name: 'x2',
          data: generateData(18, {
            min: 0,
            max: 90
          })
        },
        {
          name: 'constx2',
          data: generateData(18, {
            min: 0,
            max: 90
          })
        },
        {
          name: 'constx1',
          data: generateData(18, {
            min: 0,
            max: 90
          })
        },
        {
          name: 'x1',
          data: generateData(18, {
            min: 0,
            max: 90
          })
        },
      ],
    };
  }
  componentDidMount(){
    console.log(this.state['json']);    
    for (var key in this.state.json){
      if (key === 'var'){}
      else{
        var count = 1;
        console.log(this.state.json[key]);  
        for (var el in this.state['json'][key]){
          console.log(this.state['json'][key][el])
          this.state['json'][key][el].unshift(count)
          count += 1;
        }
      }
    }
    console.log(this.state['json']['0'])
    this.state['json']['var'].unshift('t')
    var highlight_start = 12.0;
    var highlight_end = 14.4;
  
  }
  List(){
    var xxx = function(a){
      if (a > 52)
        return "True"
      else
        return "False"
    }
    return (
      <div className="list-group list-group-flush">
          {this.state.series.map((elem) => {
            return (
              <Link key={elem.name} to={""} className="list-group-item list-group-item-action">
                  <div><b>{elem.name}</b></div>
                  <div>X val: { xxx(elem.data[0].x) }</div>
                  <div>Y val: { xxx(elem.data[0].y) }</div>
              </Link>
            );
          })}
      </div>
    );
  }
  render() {
    return (
      <Router>
      <div className="main-container">
        <div id="chart" className="row sub-container">
          <div className="col-md-6">
            <ReactApexChart options={this.state.options} series={this.state.series} type="heatmap" height="200" />
            <this.List />
	    <BarChart />
          </div>
        </div>
      <div className="row main-container">
        <div ref={this.state.div[0]} className="col-md-6 main-child"></div>
        <div ref={this.state.div[1]} className="col-md-6 main-child"></div>
        <div ref={this.state.div[2]} className="col-md-6 main-child"></div>
      </div>  
      </div>
      </Router>
    );
  }
}

export default App;
