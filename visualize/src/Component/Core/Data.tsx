// State ...
import {PropData} from "./Util/Layout";
import {Mode, Proposition} from "./Util/DataParser";
import {PropositionRenderer} from "./Renderer/PropositionRenderer";
import {ModeRenderer} from "./Renderer/ModeRenderer";

export interface PropState {
    // isEnabled is decide whether the component
    // will be showed on the screen or not.
    // if it is true, then the graph will be shown.
    isEnabled: Map<number, boolean>;

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

export interface ModeState {
    // isEnabled is decide whether the component
    // will be showed on the screen or not.
    // if it is true, then the graph will be shown.
    isEnabled: Map<number, boolean>;

    // numOfGraph represents number of child graph ui
    // it will show. e.g. if it is 0 it doesn't show any
    // graph, 1 will show 1 child graph.
    numOfGraph: number;

    modeMap: Map<number, Mode>;
}