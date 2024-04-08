import React from 'react';
import Cytoscape from 'cytoscape';
import CytoscapeComponent, { use } from 'react-cytoscapejs';
import dagre from 'cytoscape-dagre';

Cytoscape.use( dagre ); // register extension

export default function (props) {

    const vertexSize = props.vertexSize || null;
    const edgeList = props.edgeList || null;
    const hamiltonianPathEdges = props.hamiltonianPath || null;

    let vertices = []
    for (let i = 0; i < vertexSize; i++) {
        vertices.push(
            { data: { id: i, label: `${i}` } }
        )
    }

    let edges = [];
    for (const e of edgeList) {
        edges.push(
            { data: { source: e[0], target: e[1] }}
        )
    }


    let hamiltonianPath = [];
    if (hamiltonianPathEdges != null) {
        for (let i = 1; i < hamiltonianPathEdges.length; i++) {
            const u = hamiltonianPathEdges[i-1];
            const v = hamiltonianPathEdges[i];
            hamiltonianPath.push(
                { data: { source: u, target: v },
                  classes: ['hamiltonianPath']
                }
            )
        }
        let source = hamiltonianPathEdges[0];
        let target = hamiltonianPathEdges[hamiltonianPathEdges.length - 1];
        vertices[source] = { data: { id: source, label: `${source}` },
            classes: ['source']
        };
        vertices[target] = ({ data: { id: target, label: `${target}` },
            classes: ['target']
        });
    }

    const stylesheet = [
        {
            selector: 'node',
            style: {
                // 'background-color': 'red',
                'label': 'data(label)',
                'color': 'black',
                'text-valign': 'center',
                'text-halign': 'center'
            }
        },
        {
            selector: 'edge',
            style: {
                'line-color': 'gray',
                "target-arrow-shape": "triangle-backcurve",
            }
        },
        {
            selector: '.hamiltonianPath',
            style: {
                "target-arrow-shape": "triangle-backcurve",
                'line-color': 'green',
                'target-arrow-color': 'green',
                'curve-style': 'straight'
            }
        },
        {
            selector: '.source',
            style: {
                'background-color': 'red',
                'label': 'data(label)',
                'color': 'black',
                'text-valign': 'center',
                'text-halign': 'center'
            }
        },
        {
            selector: '.target',
            style: {
                'background-color': 'blue',
                'label': 'data(label)',
                'color': 'black',
                'text-valign': 'center',
                'text-halign': 'center'
            }
        },
    ];

    const layout = { name: 'cose' }

    const elements = vertices.concat(edges).concat(hamiltonianPath)

    return (
        <div>
            <CytoscapeComponent
                elements={elements}
                style={{ width: '600px', height: '600px' }}
                layout={layout}
                stylesheet={stylesheet}
            />
        </div>
    )
}