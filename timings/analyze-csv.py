#!/usr/bin/env python3

import pandas as pd
import matplotlib.pyplot as plt
import networkx as nx

GRAPHS_DATA="./graphs-data.csv"
BATCH_DATA="./computation-result-gregor.csv"
BATCH_SIZE=10

def compute_order_and_size(sig):
    g = nx.from_graph6_bytes(sig.encode("utf8"))
    return g.order(),g.size()

def generate_missing_graph_data(graph_data, outputFile):
    # Add order and size
    graph_data[["order","size"]] = graph_data["signature"].apply(compute_order_and_size).to_list()
    graph_data[["id", "order", "size"]].to_csv(outputFile, index=False)


def add_density_to_graph(graph_data):
    # Computing density
    ord = graph_data["order"]
    graph_data["density"] = graph_data["size"] / (ord * (ord - 1) / 2)
    return graph_data

def group_by_batches(run_data, graph_data, columns, operations, batch_size):
    # Group graphs by batches
    t = graph_data[columns].groupby((graph_data.index + (batch_size - (len(graph_data) % batch_size))) // batch_size, as_index=False).agg(operations)
    t.columns = ["_".join(v) for v in t.columns]
    run_data[t.columns] = t
    return run_data

def normalize_data(run_data):
    # Normalize data to better see in plots
    mn = run_data.min()
    mx = run_data.max()
    norm_data = (run_data-mn) / (mx-mn)
    return norm_data

def cummulative_data(run_data):
    # To better show a cummulative plot, we make sure the sum is 1
    plot_data = normalize_data(run_data)
    plot_data = plot_data / plot_data.sum()
    return plot_data.cumsum()

if __name__ == "__main__":
    g_data = pd.read_csv(GRAPHS_DATA)

    run_data = pd.read_csv(BATCH_DATA, names=["from", "to", "time (ms)", "mem (kb)"])

    run_data = group_by_batches(run_data, g_data, ["order", "size"], ["min", "max", "median"], BATCH_SIZE)

    print(run_data)


    print("Values for the first half of the time:")
    times = run_data["time (ms)"]
    times = times / times.sum()

    print(run_data[times.cumsum() <= 0.5])
    print(run_data[times.cumsum() <= 0.5].count() / run_data.count())

    run_data = normalize_data(run_data)
    run_data[["order_max", "size_max", "time (ms)", "mem (kb)"]].plot()
    plt.show()
