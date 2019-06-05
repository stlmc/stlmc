import React from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import { Line } from '../core/graph';
import { size, margin } from '../core/util/util'

/*
 * Props and State
 */ 
interface Props {
    jsonpath: string;
}

interface State {
    data: string;
}

/*
 * LinePlot Component
 * no longer need constructors
 * https://medium.com/@martin_hotell/react-typescript-and-defaultprops-dilemma-ca7f81c661c7
 */
class LinePlot extends React.Component<Props, State> {
    private width:number = parseFloat(styleVariable.width.replace("px", ""));
    private height:number = parseFloat(styleVariable.height.replace("px", ""));
    private width_viewer:number = parseFloat(styleVariable.width_viewer.replace("px", ""));
    private height_viewer:number = parseFloat(styleVariable.height_viewer.replace("px", ""));
    private width_controller:number = parseFloat(styleVariable.width_controller.replace("px", ""));
    private height_controller:number = parseFloat(styleVariable.height_controller.replace("px", ""));

    private margin_viewer_top:number = parseFloat(styleVariable.margin_viewer_top.replace("px",""));
    private margin_viewer_right:number = parseFloat(styleVariable.margin_viewer_right.replace("px",""));
    private margin_viewer_bottom:number = parseFloat(styleVariable.margin_viewer_bottom.replace("px",""));
    private margin_viewer_left:number = parseFloat(styleVariable.margin_viewer_left.replace("px",""));

    private margin_controller_top:number = parseFloat(styleVariable.margin_controller_top.replace("px",""));
    private margin_controller_right:number = parseFloat(styleVariable.margin_controller_right.replace("px",""));
    private margin_controller_bottom:number = parseFloat(styleVariable.margin_controller_bottom.replace("px",""));
    private margin_controller_left:number = parseFloat(styleVariable.margin_controller_left.replace("px",""));

    private line:Line = new Line(
        new size(
            this.width, 
            this.height, 
            this.width_viewer, 
            this.height_viewer, 
            this.width_controller, 
            this.height_controller
            ),
        new margin(
            this.margin_viewer_top,
            this.margin_viewer_right,
            this.margin_viewer_bottom,
            this.margin_viewer_left
        ),
        new margin(
            this.margin_controller_top,
            this.margin_controller_right,
            this.margin_controller_bottom,
            this.margin_controller_left
        ),
        // need to concat . before string of className for d3.js
        // https://www.tutorialspoint.com/d3js/d3js_selections.htm
        "."+lineplotStyle.main_theme);

    // default props
    static defaultProps:Props = {
        jsonpath: '../../Data/test.json',
    }

    // this will get error if change './data/test.json' to this.props.jsonpath
    state:State = {
        data: require('../../Data/test.json'),
    }

    componentDidMount(){
        // must invoke setdata() before draw()
        console.log();
        this.line.setdata(this.state.data);
        this.line.draw();
    }

    render() {
        return <div id="graph" className={lineplotStyle.main_theme}></div>;
    }
}

export default LinePlot;