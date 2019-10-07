import React, {createRef, useRef} from 'react';
import lineplotStyle from './style/LinePlot.module.scss';
import styleVariable from './style/variable.module.scss';
import './style/LinePlotStyle.scss';
import '../../Style/scss/main.scss';
import {margin, PropData, size} from '../Core/Util/Util';
import {ModeRenderer} from '../Core/Renderer/ModeRenderer';
import {Renderer} from '../Core/Renderer/MainRenderer';
import {PropositionRenderer} from '../Core/Renderer/PropositionRenderer';
import {Json, Mode, Proposition} from '../Core/Util/DataParser';
import Select from 'react-select';
import {ActionMeta, ValueType} from 'react-select/src/types';
import "react-tabs/style/react-tabs.css";
import Axios, {AxiosInstance} from "axios";
import {Button, Form, Toast} from 'react-bootstrap';

import {ModeState, PropState} from "../Core/Data";


/*
 * Props and State
 */
interface Props {
}


interface WorkspaceData {
    title: string;
    uid: number;
}

interface ServerError {
    message: string;
    error: boolean;
}


// State contains many useful
interface State {
    model: WorkspaceData[];
    propState: PropState;
    modeState: ModeState;

    isCounterExm: boolean;

    graphNum: number;

    xlist: number[];
    toggle: Map<number, boolean>;

    isToggleChanged: boolean;

    serverError: ServerError;
}

/*
 * LinePlot Component
 * no longer need constructors
 * https://medium.com/@martin_hotell/react-typescript-and-defaultprops-dilemma-ca7f81c661c7
 */
class LinePlot extends React.Component<Props, State> {

    private width: number = parseFloat(styleVariable.width.replace("px", ""));
    private height: number = parseFloat(styleVariable.height.replace("px", ""));
    private width_viewer: number = parseFloat(styleVariable.width_viewer.replace("px", ""));
    private height_viewer: number = parseFloat(styleVariable.height_viewer.replace("px", ""));
    private width_controller: number = parseFloat(styleVariable.width_controller.replace("px", ""));
    private height_controller: number = parseFloat(styleVariable.height_controller.replace("px", ""));

    private margin_viewer_top: number = parseFloat(styleVariable.margin_viewer_top.replace("px", ""));
    private margin_viewer_right: number = parseFloat(styleVariable.margin_viewer_right.replace("px", ""));
    private margin_viewer_bottom: number = parseFloat(styleVariable.margin_viewer_bottom.replace("px", ""));
    private margin_viewer_left: number = parseFloat(styleVariable.margin_viewer_left.replace("px", ""));

    private margin_controller_top: number = parseFloat(styleVariable.margin_controller_top.replace("px", ""));
    private margin_controller_right: number = parseFloat(styleVariable.margin_controller_right.replace("px", ""));
    private margin_controller_bottom: number = parseFloat(styleVariable.margin_controller_bottom.replace("px", ""));
    private margin_controller_left: number = parseFloat(styleVariable.margin_controller_left.replace("px", ""));


    private renderers: Renderer[] = [];
    private propRenderers: PropositionRenderer[] = [];
    private modeRenderers: ModeRenderer[] = [];
    private instance: AxiosInstance;

    private njson = new Json();

    private base_size = new size(
        this.width,
        80.0,
    );

    private graph_size = new size(
        this.width,
        this.height,
    )

    private base_margin = new margin(
        this.margin_viewer_top,
        this.margin_viewer_right,
        this.margin_viewer_bottom,
        this.margin_viewer_left
    )


    state: State = {
        isCounterExm: false,
        graphNum: 0,
        model: [],


        propState: {
            isEnabled: new Map<number, boolean>(),
            numOfGraph: 0,
            propRenderers: [],
            propMap: new Map<number, Proposition>(),
            propData: new PropData(),
        },

        modeState: {
            isEnabled: new Map<number, boolean>(),
            numOfGraph: 0,
            modeMap: new Map<number, Mode>(),
        },

        toggle: new Map<number, boolean>(),
        isToggleChanged: false,
        xlist: [],
        serverError: {
            message: "",
            error: false,
        },
    };

    constructor(props: Props) {
        super(props);

        // Set config defaults when creating the instance
        this.onModelListSelect = this.onModelListSelect.bind(this);
        this.onResetButtonClick = this.onResetButtonClick.bind(this);
        this.instance = Axios.create({baseURL: 'http://localhost:3001'});
        this.Item = this.Item.bind(this);
        this.ItemList = this.ItemList.bind(this);
        this.Main = this.Main.bind(this);
    }

    async componentDidMount() {

        console.log("ComponentDidMount");

        // get file_list
        await this.instance.get(`/file_list`)
            .catch((error) => {
                console.log(error);
                this.setState({
                    serverError: {
                        error: true,
                        message: error,
                    }
                })
            }).then((response) => {
                if (response) {
                    this.setState({
                        model:
                            response.data.file_list.map((v: string) => {
                                let [title, uid] = Object.values(v);
                                let workspace: WorkspaceData = {
                                    title: title,
                                    uid: parseInt(uid),
                                };
                                return workspace;
                            }),
                    })
                }
            })


    }

    componentDidUpdate(prevProps: Readonly<Props>, prevState: Readonly<State>, snapshot?: any): void {
        console.log("componentDidUpdate");

        if (this.state.serverError.error) {
            this.setState({
                serverError: {
                    error: false,
                    message: "",
                }
            });
        }


        console.log(this.njson.isEmpty())
        if (!this.njson.isEmpty()) {
            for (let e = 0; e < this.renderers.length; e++) {
                console.log(e);
                let intv: ([number, number][][] | undefined) = this.njson.GetGraph(e);
                if (intv) {
                    this.renderers[e].loadGraph(this.njson.xRange(e), this.njson.yRange(e), intv, this.state.xlist, this.njson.GetIntervalInfoFlat());
                }
            }


            for (let e = 0; e < this.njson.propSize; e++) {
                let d = this.njson.GetProp(e);
                if (d) {
                    this.propRenderers[e].loadGraph([this.njson.TotalMinX, this.njson.TotalMaxX], d.data, this.njson.GetIntervalInfoFlat());
                }

            }

            for (let e = 0; e < this.njson.GetModeSize(); e++) {
                let d = this.njson.GetMode(e);
                if (d) {
                    this.modeRenderers[e].loadGraph([this.njson.TotalMinX, this.njson.TotalMaxX], d.data, this.njson.GetIntervalInfoFlat());
                }

            }
        } else {
            console.log("sivalama")
            for (let e = 0; e < this.renderers.length; e++) {
                this.renderers[e].clear();
            }
            this.renderers = [];


            for (let e = 0; e < this.propRenderers.length; e++) {
                this.propRenderers[e].clear();
            }
            this.propRenderers = [];

            for (let e = 0; e < this.modeRenderers.length; e++) {
                this.modeRenderers[e].clear();
            }
            this.modeRenderers = [];
        }

    }

    // call every other event on this action.
    async onModelListSelect(value2: ValueType<{ value: string; label: string; }>, actionMeta: ActionMeta) {

        let titleVal = (value2 as { value: string; label: string; })["value"];
        let ws = this.state.model.find((value, index) => value.title == titleVal);

        // if id exists.
        if (ws != undefined) {
            let response = await this.instance.get("/file/" + ws.uid);
            console.log(response.data);

            // if no data is coming from server ...
            if (response.data != "") {
                this.njson.string = response.data;
                console.log(this.njson.variables);
                let gs = this.njson.GetGraphSize();
                console.log("GraphSize is " + gs);
                this.renderers = []
                for (let e = 0; e < gs; e++) {
                    let red = new Renderer(
                        this.graph_size, this.base_margin, e
                    );
                    red.graph = this.njson.GetGraph(e);
                    console.log(red.graph);
                    this.renderers.push(red);
                }

                let isBoolean = new Map<number, boolean>();
                this.propRenderers = [];
                for (let e = 0; e < this.njson.propSize; e++) {
                    let tmp_prop = new PropositionRenderer(
                        this.base_size, this.base_margin, e
                    );
                    this.propRenderers.push(tmp_prop);
                    isBoolean.set(e, true);
                }
                ;

                let modeIsBoolean = new Map<number, boolean>();
                this.modeRenderers = [];
                for (let e = 0; e < this.njson.GetModeSize(); e++) {
                    let md = new ModeRenderer(
                        this.base_size, this.base_margin, e
                    );
                    this.modeRenderers.push(md);
                    modeIsBoolean.set(e, true);
                }

                // get reloaded new variables.
                for (let i = 0; i < this.njson.GetGraphSize() + this.njson.propSize; i++) {
                    this.state.toggle.set(i, true);
                }

                this.setState({
                    isCounterExm: true,
                    graphNum: this.njson.GetGraphSize(),
                    xlist: this.njson.xlist,
                    propState: {
                        numOfGraph: this.njson.propSize,
                        propData: {
                            range: [this.njson.TotalMinX, this.njson.TotalMaxX],
                            interval_range: this.njson.GetIntervalInfoFlat(),
                        },
                        propRenderers: this.propRenderers,
                        propMap: this.njson.propMap,
                        isEnabled: isBoolean,
                    },
                    modeState: {
                        numOfGraph: this.njson.GetModeSize(),
                        modeMap: this.njson.modeMap,
                        isEnabled: modeIsBoolean,
                    }
                });
            } else {

                this.njson.clearAll();
                console.log(this.njson.isEmpty())

                this.setState({
                    isCounterExm: false,
                });
            }
        }
    }


    async onResetButtonClick() {
        console.log("reset called");
        let response = await this.instance.get(`/file_list`);
        this.njson.clearAll();

        //console.log(v);
        this.setState({
            isCounterExm: false,
            model:
                response.data.file_list.map((v: string) => {
                    let [title, uid] = Object.values(v);
                    let workspace: WorkspaceData = {
                        title: title,
                        uid: parseInt(uid),
                    };
                    return workspace;
                }),
        });

    }


    Item(index: number) {

        return (
            <Form.Row>
                <Form.Check
                    label={`Enabled it`}
                    checked={this.state.toggle.get(index)}
                    onClick={() => {
                        let r = this.state.toggle.get(index);
                        console.log(this.state.toggle);
                        if (r == false) {
                            this.setState({
                                isToggleChanged: true,
                                toggle:
                                    this.state.toggle.set(index, true)
                            });

                        } else {
                            this.setState({
                                isToggleChanged: true,
                                toggle:
                                    this.state.toggle.set(index, false)
                            });
                        }
                    }
                    }
                />
                <Form.Row>
                    <div className="svg_div" id={"graph" + index}
                         style={{display: this.state.toggle.get(index) ? 'block' : 'none'}}>
                        <span></span>
                    </div>
                </Form.Row>
            </Form.Row>
        )
    }

    PropUI(index: number) {
        let prop = this.state.propState.propMap.get(index);
        let isEnabled = this.state.propState.isEnabled.get(index);
        let label = "unknown";
        if (prop) {
            label = prop.name + " : " + prop.actual;
        }
        return (
            <Form.Row>
                <Form.Check
                    label={label}
                    checked={isEnabled}
                    onClick={() => {
                        let newIsEnabled = this.state.propState.isEnabled;
                        if (isEnabled) {
                            newIsEnabled.set(index, false);
                            this.setState({
                                    propState: {
                                        numOfGraph: this.state.propState.numOfGraph,
                                        propMap: this.state.propState.propMap,
                                        isEnabled: this.state.propState.isEnabled,
                                        propData: this.state.propState.propData,
                                        propRenderers: this.state.propState.propRenderers,
                                    }
                                }
                            );
                        } else {
                            newIsEnabled.set(index, true);
                            this.setState({
                                propState: {
                                    numOfGraph: this.state.propState.numOfGraph,
                                    propMap: this.state.propState.propMap,
                                    isEnabled: this.state.propState.isEnabled,
                                    propData: this.state.propState.propData,
                                    propRenderers: this.state.propState.propRenderers,
                                }
                            });
                        }
                    }
                    }
                />
                <Form.Row>
                    <div className="svg_div" id={"proposition" + index}
                         style={{display: this.state.propState.isEnabled.get(index) ? 'block' : 'none'}}>
                        <span></span>
                    </div>
                </Form.Row>
            </Form.Row>
        )
    }

    ModeUI(index: number) {

        let label = "unknown";
        let mod = this.state.modeState.modeMap.get(index);
        if (mod) {
            label = mod.name + " = " + mod.actual
        }
        let isBool = this.state.modeState.isEnabled.get(index);

        return (
            <Form.Row>
                <Form.Check
                    label={label}
                    checked={isBool}
                    onClick={() => {
                        let newIs = this.state.modeState.isEnabled;
                        if (isBool) {
                            newIs.set(index, false);
                            this.setState({
                                modeState: {
                                    isEnabled: newIs,
                                    modeMap: this.state.modeState.modeMap,
                                    numOfGraph: this.state.modeState.numOfGraph,
                                }
                            });

                        } else {
                            newIs.set(index, true);
                            this.setState({
                                modeState: {
                                    isEnabled: newIs,
                                    modeMap: this.state.modeState.modeMap,
                                    numOfGraph: this.state.modeState.numOfGraph,
                                }
                            });
                        }
                    }
                    }
                />
                <Form.Row>
                    <div className="svg_div" id={"mode" + index}
                         style={{display: this.state.modeState.isEnabled.get(index) ? 'block' : 'none'}}>
                        <span></span>
                    </div>
                </Form.Row>
            </Form.Row>
        )
    }

    ItemList() {
        let res = [];
        let res2 = [];
        let res3 = [];
        for (let i = 0; i < this.state.graphNum; i++) {
            res.push(this.Item(i));
        }
        for (let i = 0; i < this.njson.propSize; i++) {
            res2.push(this.PropUI(i));
        }

        for (let i = 0; i < this.njson.GetModeSize(); i++) {
            res3.push(this.ModeUI(i));
        }
        return (
            <Form>
                {res3}
                {res}
                {res2}
            </Form>
        )

    }

    Main() {
        return (
            <div>
                {!this.njson.isEmpty() ? (
                    <div>
                        <div className="row basic_box">
                            <div className="col-md-12">
                                <this.ItemList/>
                            </div>
                        </div>
                    </div>) : (
                    <div className="row line_plot_div">
                        <div className="col-md-1"/>
                        <div className="col-md-10 alert alert-warning" role="alert">
                            No counter example, nothing to show!
                        </div>
                        <div className="col-md-1"/>
                    </div>
                )}
            </div>
        )
    }

    render() {
        // TODO: Update precision of graph after update.
        return (
            <div>
                <div className="row">
                    <div className="col-md-1"/>
                    <div className="col-md-10">
                        <label>Models</label>
                        <Select isSearchable={true} options={this.state.model.map(
                            (v) => {
                                return ({value: v.title, label: v.title});
                            }
                        )} onChange={this.onModelListSelect}/>
                    </div>
                    <div className="col-md-1">
                        <Button variant="outline-dark" onClick={this.onResetButtonClick} id="non-outline">reset</Button>
                    </div>
                </div>
                <this.Main/>


            </div>);
    }
}

export default LinePlot;