import pandas as pd
import numpy as np
import matplotlib
import pylab as pl
import matplotlib.pyplot as plt
import matplotlib.cm as cm


# Use PDF for matplotlib output
matplotlib.use('PDF')



def main():
    perfArtemisWhynot()
    # Uncomment to use this function
    # perfSingleDerWhynot()

def perfArtemisWhynot():
    
    name = 'sensor_com_laser'
    dfwnq2 = pd.read_csv(str(name) + '.csv', sep=",")
    
    axwnq2 = dfwnq2[['Laserlight', 'DGpatt ']].plot.bar(width=0.7, color=['#6A0572', '#F5C518'])

    legend = axwnq2.legend(bbox_to_anchor=(-0.025, 1.036), prop={'size': 20}, labels=['Laserlight', 'DGpatt '], loc=2,
              borderpad=0.1, labelspacing=0, handlelength=1, handletextpad=0.2,
              columnspacing=0.5, framealpha=1, ncol=1)
    legend.get_frame().set_edgecolor('black')
    
    # Axis labels and ticks
    axwnq2.set_ylabel('Runtime (sec)', fontsize=28)
    axwnq2.set_xlabel('Datasets', fontsize=25)

    axwnq2.set_xticks(range(len(dfwnq2.provSize)))
    axwnq2.set_xticklabels(['1K', '10K', '100K', '1M', '4M'], fontsize=22)
    
    pl.xticks(rotation=0)
    axwnq2.set_yscale("log")
    pl.ylim([0.01, 3000])
    pl.yticks(fontsize=24)

    # Grid settings
    axwnq2.yaxis.grid(which='major', linewidth=3.0, linestyle=':')
    axwnq2.set_axisbelow(True)
 # second x-axis
    ax2 = axwnq2.twiny()
    ax2.xaxis.set_ticks_position('bottom') # set the position of the second x-axis to bottom
    ax2.xaxis.set_label_position('bottom') # set the position of the second x-axis to bottom
    ax2.spines['bottom'].set_position(('outward', 80))

    ax2.set_xlabel("Query Result Size",fontsize=26)
    # ax2.xaxis.labelpad = 12
    ax2.set_xlim(0, 60)
    ax2.set_xticklabels(['0','10','745','59.7K','1M'],fontsize=24)
    ax2.set_xticks([7, 18, 30, 42, 53])

    ax2.set_frame_on(True)
    ax2.patch.set_visible(False)
    ax2.spines["bottom"].set_visible(True)

    pl.savefig(str(name) + '.pdf', bbox_inches='tight')
    pl.cla()

def perfSingleDerWhynot():
    name = 'singlederi-whynot'
    dfwnq2 = pd.read_csv(str(name) + '.csv', sep=",")
    
    axwnq2 = dfwnq2[['Naive', 'DGpatt ']].plot.bar(width=0.7, color=['#E7D501', '#F43B00'])

    legend = axwnq2.legend(bbox_to_anchor=(-0.025, 1.036), prop={'size': 20}, labels=['Naive', 'DGpatt '], loc=2,
              borderpad=0.1, labelspacing=0, handlelength=1, handletextpad=0.2,
              columnspacing=0.5, framealpha=1, ncol=1)
    legend.get_frame().set_edgecolor('black')

    # Axis labels and ticks
    axwnq2.set_ylabel('Runtime (sec)', fontsize=28)
    axwnq2.set_xlabel('Datasets', fontsize=25)

    axwnq2.set_xticks(range(len(dfwnq2.provSize)))
    axwnq2.set_xticklabels(['1e7', '1e8', '1e9', '1e10', '2e11'], fontsize=22)
    
    pl.xticks(rotation=0)
    axwnq2.set_yscale("log", nonposy='clip')
    pl.ylim([0.01, 3000])

    for tick in axwnq2.xaxis.get_major_ticks():
        tick.label.set_fontsize(24)
    for tick in axwnq2.yaxis.get_major_ticks():
        tick.label.set_fontsize(28)

    # Grid settings
    axwnq2.yaxis.grid(which='major', linewidth=3.0, linestyle=':')
    axwnq2.set_axisbelow(True)

     # second x-axis
    ax2 = axwnq2.twiny()
    ax2.xaxis.set_ticks_position('bottom') # set the position of the second x-axis to bottom
    ax2.xaxis.set_label_position('bottom') # set the position of the second x-axis to bottom
    ax2.spines['bottom'].set_position(('outward', 80))

    ax2.set_xlabel("Query Result Size",fontsize=26)
    # ax2.xaxis.labelpad = 12
    ax2.set_xlim(0, 60)
    ax2.set_xticklabels(['0','10','745','59.7K','1M'],fontsize=24)
    ax2.set_xticks([7, 18, 30, 42, 53])

    ax2.set_frame_on(True)
    ax2.patch.set_visible(False)
    ax2.spines["bottom"].set_visible(True)

    pl.savefig(str(name) + '.pdf', bbox_inches='tight')
    pl.cla()

if __name__ == "__main__":
    main()
