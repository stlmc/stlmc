import React from 'react';
import './style/LinePlot.scss';
import { Line } from './core/graph';
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
    private line:Line = new Line();

    // default props
    static defaultProps:Props = {
        jsonpath: '../Data/test.json',
    }

    // this will get error if change './data/test.json' to this.props.jsonpath
    state:State = {
        data: require('../Data/test.json'),
    }

    componentDidMount(){
        // must invoke setdata() before draw()
        this.line.setdata(this.state.data);
        this.line.draw();
    }

    render() {
        return <div id="graph" className="main_theme"></div>;
    }
}

export default LinePlot;