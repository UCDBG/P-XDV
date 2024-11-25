import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import matplotlib.ticker as ticker

def main():
    perf_single_line_chart()

def perf_single_line_chart():
    # Assuming you have a DataFrame 'data' with multiple data points for each category
    data = pd.DataFrame({
        'TOP_K': ['1', '3', '5', '10', '20'],
        'aqi_q1': [5.332955352, 5.340306657, 5.356535978, 5.366447652, 5.436840187],
        'aqi_q2': [23.840078348, 23.913850804, 23.998125453, 24.177226126, 24.490901678],
        'wisdm_q2': [0.135121679, 0.132076594, 0.135533459, 0.135830866, 0.131202622],
        'wisdm_q3': [0.159116952, 0.158436371, 0.161172995, 0.160652503, 0.162891060]
    })    
    
    fig, ax = plt.subplots()
    
    # Plotting each category's data points separately
    ax.plot(data['TOP_K'], data['aqi_q1'], marker='o', markersize=10, label='aqi_q1')
    ax.plot(data['TOP_K'], data['aqi_q2'], marker='o', markersize=10, label='aqi_q2')
    ax.plot(data['TOP_K'], data['wisdm_q2'], marker='o', markersize=10, label='wisdm_q2')
    ax.plot(data['TOP_K'], data['wisdm_q3'], marker='o', markersize=10, label='wisdm_q3')

    ax.set_ylabel('Runtime (sec)', fontsize=28)
    ax.set_xlabel('TOP_K', fontsize=25)
    ax.set_xticklabels(data['TOP_K'], fontsize=22)
    ax.legend(prop={'size': 20}, ncol=2, loc='upper right', bbox_to_anchor=(1, 1))
    # prop={'size': 12}, loc='upper right', bbox_to_anchor=(1, 1))

    # Set y-axis limits and scale to log
    ax.set_yscale("log")
    plt.ylim([0.01, 3000])
    plt.yticks(fontsize=24)

    plt.savefig('topk.pdf', bbox_inches='tight')
    plt.show()

if __name__ == "__main__":
    main()
