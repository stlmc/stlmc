import React from 'react';
import './style/LinePlot.scss';
import { Line } from './core/graph';
/*
 * Props and State
 */ 
interface Props {

}

interface State {
    
}

/*
 * LinePlot Component
 */
class LinePlot extends React.Component<State> {
    private line:Line = new Line();
    constructor (props: Props){
        super(props);
    }

    componentDidMount(){
        this.line.draw();
    }

    render() {
        return <div id="graph" className="main_theme"></div>;
    }
}

export default LinePlot;