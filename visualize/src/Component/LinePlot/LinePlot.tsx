import React from 'react';
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
import {Button, Form, Modal, Spinner} from 'react-bootstrap';
import $ from 'jquery';
import {ModeState, PropState} from "../Core/Data";


/*
 * Props and State
 */
interface Props {
    url: string;
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
    isOptionAlive: boolean;
    selectedValue: string;
    propState: PropState;
    modeState: ModeState;

    isCounterExm: boolean;

    graphNum: number;

    xlist: number[];
    toggle: Map<number, boolean>;

    isToggleChanged: boolean;

    serverError: ServerError;
    isShutDown: boolean;
    isLoadingReset: boolean;
}

/*
 * LinePlot Component
 * no longer need constructors
 * https://medium.com/@martin_hotell/react-typescript-and-defaultprops-dilemma-ca7f81c661c7
 */
class LinePlot extends React.Component<Props, State> {

    private width: number = parseFloat(styleVariable.width.replace("px", ""));
    private height: number = parseFloat(styleVariable.height.replace("px", ""));

    private margin_viewer_top: number = parseFloat(styleVariable.margin_viewer_top.replace("px", ""));
    private margin_viewer_right: number = parseFloat(styleVariable.margin_viewer_right.replace("px", ""));
    private margin_viewer_bottom: number = parseFloat(styleVariable.margin_viewer_bottom.replace("px", ""));
    private margin_viewer_left: number = parseFloat(styleVariable.margin_viewer_left.replace("px", ""));


    private renderers: Renderer[] = [];
    private propRenderers: PropositionRenderer[] = [];
    private modeRenderers: ModeRenderer[] = [];
    private instance: AxiosInstance;

    private njson = new Json();

    private base_margin = new margin(
        this.margin_viewer_top,
        this.margin_viewer_right,
        this.margin_viewer_bottom,
        this.margin_viewer_left
    );


    state: State = {
        isCounterExm: false,
        selectedValue: "",
        isOptionAlive: false,
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
        isShutDown: false,
        isLoadingReset: false,
    };

    constructor(props: Props) {
        super(props);

        // Set config defaults when creating the instance
        this.onModelListSelect = this.onModelListSelect.bind(this);
        this.onResetButtonClick = this.onResetButtonClick.bind(this);
        this.onOffButtonClick = this.onOffButtonClick.bind(this);
        this.instance = Axios.create({baseURL: this.props.url});
        this.Item = this.Item.bind(this);
        this.ItemList = this.ItemList.bind(this);
        this.Main = this.Main.bind(this);
        this.ShutDown = this.ShutDown.bind(this);
        this.LoadingBtn = this.LoadingBtn.bind(this);
    }

    async componentDidMount() {
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
        if (this.state.serverError.error) {
            this.setState({
                serverError: {
                    error: false,
                    message: "",
                }
            });
        }

        if (!this.njson.isEmpty()) {
            let modeRenderersXScale = [];
            let modeRenderersYScale = [];
            for (let e = 0; e < this.njson.GetModeSize(); e++) {
                let d = this.njson.GetMode(e);
                if (d) {
                    this.modeRenderers[e].loadGraph([this.njson.TotalMinX, this.njson.TotalMaxX], d.data, this.njson.GetIntervalInfoFlat(), d.originalData, d.type, d.min, d.max);
                    modeRenderersXScale.push(this.modeRenderers[e].getXscale());
                    modeRenderersYScale.push(this.modeRenderers[e].getYscale());
                }

            }
            for (let e = 0; e < this.renderers.length; e++) {
                let eGraph: (Map<string, [number, number][]> | undefined) = this.njson.GetDataByName(e);
                if (eGraph) {
                    // vardict should always exist or undefined error would occur!
                    this.renderers[e].loadGraph(this.njson.xRange(e), this.njson.yRange(e), eGraph, this.state.xlist, this.njson.GetIntervalInfoFlat(), this.njson.variables, this.njson.GetModeSize(), modeRenderersXScale, modeRenderersYScale);
                }
            }


            for (let e = 0; e < this.njson.propSize; e++) {
                let d = this.njson.GetProp(e);
                if (d) {
                    this.propRenderers[e].loadGraph([this.njson.TotalMinX, this.njson.TotalMaxX], d.data, this.njson.GetIntervalInfoFlat());
                }

            }
        } else {
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
        console.log(titleVal);
        let ws = this.state.model.find((value, index) => value.title == titleVal);

        // if id exists.
        if (ws != undefined) {
            let response = await this.instance.get("/file/" + ws.uid);
            // if no data is coming from server ...
            if (response.data != "") {
                this.njson.string = response.data;
                let gs = this.njson.GetGraphSize();
                this.renderers = [];
                let isRedBool = new Map<number, boolean>();

                let width = $(window).width();
                if (width){
                    width = width * 0.8 - this.base_margin.left - this.base_margin.right;
                }
                let newSize = new size(
                    width,
                    80.0
                );

                for (let e = 0; e < gs; e++) {
                    let red = new Renderer(
                        new size(
                            width,
                            this.height
                        ), this.base_margin, e
                    );
                    red.graph = this.njson.GetGraph(e);
                    this.renderers.push(red);
                    isRedBool.set(e, true);
                }

                let isBoolean = new Map<number, boolean>();
                this.propRenderers = [];
                for (let e = 0; e < this.njson.propSize; e++) {
                    let tmp_prop = new PropositionRenderer(
                        newSize, this.base_margin, e
                    );
                    this.propRenderers.push(tmp_prop);
                    isBoolean.set(e, true);
                }
                ;

                let modeIsBoolean = new Map<number, boolean>();
                this.modeRenderers = [];
                for (let e = 0; e < this.njson.GetModeSize(); e++) {
                    let md = new ModeRenderer(
                        newSize, this.base_margin, e
                    );
                    this.modeRenderers.push(md);
                    modeIsBoolean.set(e, true);
                }

                // get reloaded new variables.
                for (let i = 0; i < this.njson.GetGraphSize() + this.njson.propSize; i++) {
                    this.state.toggle.set(i, true);
                }

                this.setState({
                    selectedValue: titleVal,
                    isOptionAlive: true,
                    isCounterExm: true,
                    toggle: isRedBool,
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

                this.setState({
                    isCounterExm: false,
                });
            }
        }
    }

    async onOffButtonClick() {
        let response = await this.instance.get(`/shutdown`);
        if (response.data == "Shutdown called"){
            console.log("server shutdown.. you need to restart server for progress!");
            this.setState({isShutDown: true,});
        }
    }

    async onResetButtonClick() {
        this.setState({isLoadingReset: true});
        let response = await this.instance.get(`/file_list`);
        this.njson.clearAll();
        this.setState({
            isOptionAlive: false,
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
            isLoadingReset: false,
        });

    }


    Item(index: number, margin: number|undefined) {
        let vars = this.njson.GetVar(index);
        let isEnabled = this.state.toggle.get(index);
        let label = "unknown";
        if(vars){
            label = "Var: ";
            for (let i = 0; i < vars.length; i++){
                if (i==0)
                    label += vars[i];
                else
                    label += (", "+vars[i]);
            }
        }

        return (
            <div style={{marginLeft: margin, marginRight: margin}}>
            <Form.Row>
                <Form.Check
                    label={label}
                    checked={isEnabled}
                    onClick={() => {
                        let newIsEnabled = this.state.toggle;
                        if (isEnabled) {
                            newIsEnabled.set(index, false)
                            this.setState({
                                toggle: newIsEnabled,
                            });

                        } else {
                            newIsEnabled.set(index, true)
                            this.setState({
                                toggle: newIsEnabled,
                            });
                        }
                    }
                    }
                />
                <Form.Row>
                    <div id={"graph" + index} style={{display: this.state.toggle.get(index) ? 'block' : 'none'}}>
                        <span></span>
                    </div>
                </Form.Row>
            </Form.Row>
            </div>
        )
    }

    PropUI(index: number, margin: number|undefined) {
        let prop = this.state.propState.propMap.get(index);
        let isEnabled = this.state.propState.isEnabled.get(index);
        let label = "unknown";
        if (prop) {
            label = prop.name + " : " + prop.actual;
        }
        return (
            <div style={{marginLeft: margin, marginRight: margin}}>
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
            </div>
        )
    }

    ModeUI(index: number, margin: number|undefined) {

        let label = "unknown";
        let mod = this.state.modeState.modeMap.get(index);
        if (mod) {
            label = mod.name + " = " + mod.actual
        }
        let isBool = this.state.modeState.isEnabled.get(index);

        return (
            <div style={{marginLeft: margin, marginRight: margin}}>
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
            </div>
        )
    }

    ItemList() {
        let res = [];
        let res2 = [];
        let res3 = [];
        let margin = $(window).width();
        if (margin){
            margin = margin * 0.1 + this.base_margin.left;
        }

        for (let i = 0; i < this.state.graphNum; i++) {
            res.push(this.Item(i, margin));
        }
        for (let i = 0; i < this.njson.propSize; i++) {
            res2.push(this.PropUI(i, margin));
        }

        for (let i = 0; i < this.njson.GetModeSize(); i++) {
            res3.push(this.ModeUI(i, margin));
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

    ShutDown(){
        return (
            <Modal
                show={this.state.isShutDown}
                size="lg"
                aria-labelledby="contained-modal-title-vcenter"
                centered
                keyboard={false}
                backdrop={'static'}
            >
                <Modal.Header>
                    <Modal.Title id="contained-modal-title-vcenter">
                        Visualize Server shutdown
                    </Modal.Title>
                </Modal.Header>
                <Modal.Body>
                    <p>
                        Visualize server has been successfully shutdowned. Restart the server to use visualization.
                    </p>
                </Modal.Body>
            </Modal>
        )
    }

    LoadingBtn(){
        return(
            <Spinner
                as="span"
                animation="border"
                size="sm"
                role="status"
                aria-hidden="true"
            />
        )
    }

    render() {
        let selected = this.state.selectedValue;
        let select = this.state.isOptionAlive ? {value: selected, label: selected} : null;
        // TODO: Update precision of graph after update.
        return (
            <div>
                <div className="row">
                    <div className="col-md-11"/>
                    <div className="col-md-1">
                        <Button variant="outline-danger" onClick={this.onOffButtonClick} id="non-outline">off</Button>
                    </div>
                </div>
                <div className="row">
                    <div className="col-md-1"/>
                    <div className="col-md-10">
                        <label>Models</label>
                        <Select isSearchable={true} value={select} options={this.state.model.map(
                            (v) => {
                                return ({value: v.title, label: v.title});
                            }
                        )} onChange={this.onModelListSelect} />
                    </div>
                    <div className="col-md-1">
                    </div>
                </div>
                <div className="row items-7">
                    <div className="col-md-10"/>
                    <div className="col-md-1 text-right">
                        <Button variant="outline-dark" onClick={this.onResetButtonClick} id="non-outline">
                            {this.state.isLoadingReset ? <this.LoadingBtn/> : "reset"}
                        </Button>
                    </div>
                    <div className="col-md-1"/>
                </div>
                {this.state.isShutDown ? <this.ShutDown/> : <this.Main/>}
            </div>);
    }
}

export default LinePlot;
