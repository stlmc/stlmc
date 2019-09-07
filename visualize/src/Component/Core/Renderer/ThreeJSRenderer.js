import * as THREE from 'three';
import $ from "jquery";

class ThreeRenderer {


    constructor(){
        this.scene = new THREE.Scene();
        this.camera = new THREE.PerspectiveCamera( 75, window.innerWidth / window.innerHeight, 0.1, 1000 );

        this.renderer = new THREE.WebGLRenderer();
        this.renderer.setSize( window.innerWidth, window.innerHeight );
    }

    setAndStart(doc){
        //document.body.appendChild( this.renderer.domElement );
        //$('#threeCanvas').appendChild( this.renderer.domElement );
        console.log(doc);
        //doc.appendChild( this.renderer.domElement );


        let geometry = new THREE.BoxGeometry( 1, 1, 1 );
        let material = new THREE.MeshBasicMaterial( { color: 0x00ff00 } );
        let cube = new THREE.Mesh( geometry, material );
        this.scene.add( cube );

        this.camera.position.z = 5;

        //this.animate();
    }

    animate() {
        requestAnimationFrame( this.animate );
        this.renderer.render( this.scene, this.camera );
    }


}



export {ThreeRenderer};