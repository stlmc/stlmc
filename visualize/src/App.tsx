import React from 'react';
import logo from './logo.svg';
import './App.css';
import './Style/scss/main.scss';
import { Link } from 'react-router-dom';
import { Switch, BrowserRouter as Router, Route } from 'react-router-dom';
import LinePlot from './Component/LinePlot';


const App: React.FC = () => {
  return (
    <div><LinePlot/></div>
  );
}
/*
const App: React.FC = () => {
  return (
    <div className="App">
      <header className="App-header">
        <LinePlot />
        <img src={logo} className="App-logo" alt="logo" />
        <p>
          Edit <code>src/App.tsx</code> and save to reload.
        </p>
        <a
          className="App-link"
          href="https://reactjs.org"
          target="_blank"
          rel="noopener noreferrer"
        >
          Learn React
        </a>
      </header>
    </div>
  );
}
*/
export default App;
