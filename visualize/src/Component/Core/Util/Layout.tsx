export class margin {
    constructor(
        public top: number = 0.0,
        public right: number = 0.0,
        public bottom: number = 0.0,
        public left: number = 0.0,
    ) {
    }
}

export class size {
    constructor(
        public width: number = 0.0,
        public height: number = 0.0,
    ) {
    }
}

export class PropData {
    constructor(
        // range of x, for example if your data start with 0 and
        // end with 22.2 then, range will be [0, 22.2]
        public range: number[] = [],
        // interval_range is same as range but contains start and
        // end points of every intervals.
        // For example, if the interval range of each a : [0, 1], b : [1, 3]
        // then, interval_range will be [0, 1, 3].
        public interval_range: number[] = [],
    ) {
    }
}