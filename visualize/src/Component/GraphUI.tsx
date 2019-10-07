import React from 'react';
import {Form} from "react-bootstrap";
import {PropositionRenderer} from "./Core/Renderer/PropositionRenderer";
import {margin, size, PropData} from "./Core/Util/Layout";
import {Proposition} from "./Core/Util/DataParser";

// Props have immutable data.
interface Props {
}


// State ...
interface State {
    // isEnabled is decide whether the component
    // will be showed on the screen or not.
    // if it is true, then the graph will be shown.
    isEnabled: Boolean[];

    // numOfGraph represents number of child graph ui
    // it will show. e.g. if it is 0 it doesn't show any
    // graph, 1 will show 1 child graph.
    numOfGraph: number;

    // DataGraphUI will have innerly main graph's renderers list.
    propRenderers: PropositionRenderer[];

    // The data that will be drawn by propRenderers.
    propData: PropData;

    propMap: Map<number, Proposition>;
}


/**
 * PropGraphUI implements counter-example's graph plot.
 */
class PropGraphUI extends React.Component<Props, State> {

    state: State = {
        isEnabled: [],
        numOfGraph: 0,
        propRenderers: [],
        propMap: new Map<number, Proposition>(),
        propData: new PropData(),
    }

    constructor(props: Props) {
        super(props);


        // bind basic ui for react component;
        this.BaseUI = this.BaseUI.bind(this);
        this.UpdateGraph = this.UpdateGraph.bind(this);

    }

    UpdateGraph(numOfGraph: number, s: size, m: margin, propData: PropData, propMap: Map<number, Proposition>) {
        let boolList: Boolean[] = [];
        let tmp = [];

        for (let i = 0; i < numOfGraph; i++) {
            boolList.push(true);
            let tmp_mainRenderer = new PropositionRenderer(
                s, m, i
            );
            tmp.push(tmp_mainRenderer);
        }

        this.setState({
            numOfGraph: numOfGraph,
            isEnabled: boolList,
            propData: propData,
            propRenderers: tmp,
            propMap: propMap,
        });
    }

    // Initialize any datastructure when this compoment
    // is loaded (actually, after mounted).
    componentDidMount(): void {
        this.setState({
            isEnabled: [],
            numOfGraph: 0,
            propRenderers: [],
        })
    }

    componentDidUpdate(prevProps: Readonly<Props>, prevState: Readonly<State>, snapshot?: any): void {
        console.log("hello");
        let propData = this.state.propData;

        for (let e = 0; e < this.state.numOfGraph; e++) {
            let prop = this.state.propMap.get(e);
            if (prop) {
                this.state.propRenderers[e].loadGraph(propData.range, prop.data, propData.interval_range);
            }
        }

    }

    BaseUI(index: number) {
        let isEnabled = this.state.isEnabled[index];
        return (
            <Form.Row>
                <Form.Check
                    label={`Enabled it`}
                    checked={true}
                    onClick={() => {
                        if (isEnabled) {
                            this.setState({
                                isEnabled: this.state.isEnabled.map((v, k) => {
                                    return k == index ? false : v;
                                }),
                            });
                        } else {
                            this.setState({
                                isEnabled: this.state.isEnabled.map((v, k) => {
                                    return k == index ? true : v;
                                }),
                            });
                        }
                    }
                    }
                />
                <Form.Row>
                    <div className="svg_div" id={"proposition" + index}
                         style={{display: this.state.isEnabled ? 'block' : 'none'}}>
                        <span></span>
                    </div>
                </Form.Row>
            </Form.Row>
        )
    }

    render() {
        let ui = [];
        for (let i = 0; i < this.state.numOfGraph; i++) {
            ui.push(this.BaseUI(i));
        }

        return (
            <Form>
                {ui}
            </Form>
        )
    }

    // Item2(index: number){
    //
    //     return (
    //         <Form.Row>
    //             <Form.Check
    //                 label={`Enabled it`}
    //                 checked={this.state.toggle.get(index)}
    //                 onClick={() => {
    //                     let r = this.state.toggle.get(index);
    //                     console.log(this.state.toggle);
    //                     if (r == false) {
    //                         this.setState({
    //                             isToggleChanged: true,
    //                             toggle:
    //                                 this.state.toggle.set(index, true)
    //                         });
    //
    //                     } else {
    //                         this.setState({
    //                             isToggleChanged: true,
    //                             toggle:
    //                                 this.state.toggle.set(index, false)
    //                         });
    //                     }
    //                 }
    //                 }
    //             />
    //             <Form.Row>
    //                 <div className="svg_div" id={"proposition"+index} style={{display: this.state.toggle.get(index) ? 'block' : 'none' }}>
    //                     <span></span>
    //                 </div>
    //             </Form.Row>
    //         </Form.Row>
    //     )
    // }
    //
    // Item3(index: number){
    //
    //     return (
    //         <Form.Row>
    //             <Form.Check
    //                 label={`Enabled it`}
    //                 checked={this.state.toggle.get(index)}
    //                 onClick={() => {
    //                     let r = this.state.toggle.get(index);
    //                     console.log(this.state.toggle);
    //                     if (r == false) {
    //                         this.setState({
    //                             isToggleChanged: true,
    //                             toggle:
    //                                 this.state.toggle.set(index, true)
    //                         });
    //
    //                     } else {
    //                         this.setState({
    //                             isToggleChanged: true,
    //                             toggle:
    //                                 this.state.toggle.set(index, false)
    //                         });
    //                     }
    //                 }
    //                 }
    //             />
    //             <Form.Row>
    //                 <div className="svg_div" id={"mode"+index} style={{display: this.state.toggle.get(index) ? 'block' : 'none' }}>
    //                     <span></span>
    //                 </div>
    //             </Form.Row>
    //         </Form.Row>
    //     )
    // }
    //
    // ItemList(){
    //     let res = [];
    //     let res2 = [];
    //     let res3 = [];
    //     for(let i = 0; i < this.state.graphNum; i++){
    //         res.push(this.Item(i));
    //     }
    //     for(let i = 0; i < this.njson.propSize; i++){
    //         console.log("hhh");
    //         res2.push(this.Item2(i));
    //     }
    //
    //     for(let i = 0; i < this.njson.GetModeSize(); i++){
    //         console.log("hhh");
    //         res3.push(this.Item3(i));
    //     }
    //     return (
    //         <Form>
    //             {res3}
    //             {res}
    //             {res2}
    //         </Form>
    //     )
    //
    // }
}

export {PropGraphUI}