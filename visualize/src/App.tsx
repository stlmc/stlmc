import React from 'react';
import './App.css';
import './Style/scss/main.scss';
import 'bootstrap/dist/css/bootstrap.min.css';
import LinePlot from './Component/LinePlot/LinePlot';


const App: React.FC = () => {
  let option = require('./.option.json');
  console.log(option.url);
  return (
    <div className="main-container"><LinePlot url={option.url}/></div>
  );
};

export default App;
