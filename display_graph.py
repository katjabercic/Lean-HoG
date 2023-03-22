import sys
import os
import re
import time
import pandas as pd
import matplotlib.pyplot as plt
import numpy as np
import numpy.polynomial.polynomial as poly
from argparse import ArgumentParser


def display(data):
    plt.ion()

    plt.figure(figsize=(27,7))
    while True:
        df = pd.read_csv("tests/" + data)
        curr_graph = df['id'].iloc[-1]
        max_ind = 17 * 100 + 1
        total_time = df['time'].sum()
        avg_time = total_time / len(df['id'])

        plt.subplot(131)
        plt.bar(df['id'], df['time'], width=10, align='edge')
        plt.xlabel('id')
        plt.ylabel('time(s)')

        plt.subplot(132)
        plt.scatter(df['vertex_size'], df['time'])
        plt.xlabel('vertex_size')
        plt.ylabel('time(s)')

        plt.subplot(133)
        plt.scatter(df['edge_size'], df['time'])
        plt.xlabel('edge_size')
        plt.ylabel('time(s)')

        plt.suptitle(data + f'\nProcessing graphs: {curr_graph} / {max_ind}, total elapsed time: {total_time:.2f} s, average time: {avg_time:.2f} s')
        plt.pause(3)
        plt.clf()

if __name__ == "__main__":
    arg_parser = ArgumentParser()
    arg_parser.add_argument("--data", required=True, dest="data",
                        help="Data for which to display the graph")
    args = arg_parser.parse_args()

    if not os.path.exists(f'tests/{args.data}'):
        print(f'Data file tests/{args.data} not found!')
        sys.exit(1)

    display(args.data)