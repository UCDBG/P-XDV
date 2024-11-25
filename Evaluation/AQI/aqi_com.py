import pandas as pd
import numpy as np
from numpy import arange,power
import matplotlib
import pylab as pl
import matplotlib.pyplot as plt
import matplotlib.cm as cm
matplotlib.use('PDF')


def main():
    perfArtemisWhynot()
    #perfSingleDerWhynot()



def perfArtemisWhynot():
    name='aqi_com'
    dfwnq2=pd.read_csv(str(name) + '.csv',sep=",")
    
    # group_label=list(dfwnq2['provSize'].unique())
    # pl.ioff()

    # axwnq2=dfwnq2[['100','1000','10000','FULL']].plot.bar(width=0.9)
    axwnq2=dfwnq2[['Naive','DG']].plot.bar(width=0.7, color=['#00389F','#F43B00'])

    legend = axwnq2.legend(bbox_to_anchor=(-0.025, 1.036),prop={'size': 20},labels=['Naive','DG'],loc=2,
              borderpad=0.1,labelspacing=0,handlelength=1,handletextpad=0.2,
              columnspacing=0.5,framealpha=1,ncol=1)
    legend.get_frame().set_edgecolor('black')
    
    # axis labels and tics
    axwnq2.set_ylabel('Runtime (sec)', fontsize=28)
    axwnq2.set_xlabel('Datasets', fontsize=25) 

    # axwnq2.set_xscale("symlog",linthreshx=4e6)
    # pl.xlim([min(dfwnq2.provSize),max(dfwnq2.provSize)])

    axwnq2.set_xticks(range(len(dfwnq2.provSize)))
    axwnq2.set_xticklabels(['1K','10K','100K','1M'],fontsize=22)   

    #axwnq2.set_xticks([6, 16, 25, 35, 45, 55]) 
    #axwnq2.set_xticklabels(dfwnq2.provSize)

    #labels = [item.get_text() for item in axwnq2.get_xticklabels()]
    #labels[0] = '1e11'
    #labels[1] = '1e12'
    #labels[2] = '1e14'
    #labels[3] = '6e14'
    #labels[4] = '1e15'
    #axwnq2.set_xticklabels(labels, fontsize = 20)

    #axwnq2.tick_params(labelsize=10)
    pl.xticks(rotation=0)

    axwnq2.set_yscale("log") #, nonposy='clip')
    # pl.ylim([0.01, max(dfwnq2['100'] + dfwnq2['1000'] + dfwnq2['10000'])])
    pl.ylim([0.01,3000])
    pl.yticks(fontsize = 24) 

    # for tick in axwnq2.xaxis.get_major_ticks():
    #     tick.label.set_fontsize(24) 

    # for tick in axwnq2.yaxis.get_major_ticks():
    #     tick.label.set_fontsize(28) 

    # second x-axis
    # ax2 = axwnq2.twiny()
    # ax2.set_xlabel("Datasize",fontsize=25)
    # ax2.xaxis.labelpad = 12
    # ax2.set_xlim(0, 60)
    # ax2.set_xticks([7, 18, 30, 42, 53])
    # ax2.set_xticklabels(['1K','10K','100K','1M','20M'], fontsize=25)

    # grid
    axwnq2.yaxis.grid(which='major',linewidth=3.0,linestyle=':')
    axwnq2.set_axisbelow(True)

    # second x-axis
    # ax2 = axwnq2.twiny()
    # ax2.xaxis.set_ticks_position('bottom') # set the position of the second x-axis to bottom
    # ax2.xaxis.set_label_position('bottom') # set the position of the second x-axis to bottom
    # ax2.spines['bottom'].set_position(('outward', 80))

   #  ax2.set_xlabel("Query Result Size",fontsize=26)
    # ax2.xaxis.labelpad = 12
    # ax2.set_xlim(0, 60)
    # ax2.set_xticklabels(['46','5.4K','171K','3.8M'],fontsize=24)
    # ax2.set_xticks([8, 23, 38, 52])

    # ax2.set_frame_on(True)
    # ax2.patch.set_visible(False)
    # ax2.spines["bottom"].set_visible(True)

    # pl.show()
    pl.savefig(str(name) + '.pdf', bbox_inches='tight')
    pl.cla()


def perfSingleDerWhynot():
    name='singlederi-whynot'
    dfwnq2=pd.read_csv(str(name) + '.csv',sep=",")
    # print(dfwnq2)
    
    # group_label=list(dfwnq2['provSize'].unique())
    # pl.ioff()

    # axwnq2=dfwnq2[['100','1000','10000','FULL']].plot.bar(width=0.9)
    axwnq2=dfwnq2[['Naive','DG']].plot.bar(width=0.7, color=['#E7D501','#F43B00'])

    legend = axwnq2.legend(bbox_to_anchor=(-0.025, 1.036),prop={'size': 20},labels=['Naive','DG'],loc=2,
              borderpad=0.1,labelspacing=0,handlelength=1,handletextpad=0.2,
              columnspacing=0.5,framealpha=1,ncol=1)
    legend.get_frame().set_edgecolor('black')
    
    # axis labels and tics
    axwnq2.set_ylabel('Runtime (sec)', fontsize=28)
    axwnq2.set_xlabel('Datasets', fontsize=25) 

    # axwnq2.set_xscale("symlog",linthreshx=4e6)
    # pl.xlim([min(dfwnq2.provSize),max(dfwnq2.provSize)])

    axwnq2.set_xticks(range(len(dfwnq2.provSize)))
    axwnq2.set_xticklabels(['1e7','1e8','1e9','1e10','2e11'],fontsize=22)   
    #axwnq2.set_xticks([6, 16, 25, 35, 45, 55]) 
    #axwnq2.set_xticklabels(dfwnq2.provSize)

    #labels = [item.get_text() for item in axwnq2.get_xticklabels()]
    #labels[0] = '1e11'
    #labels[1] = '1e12'
    #labels[2] = '1e14'
    #labels[3] = '6e14'
    #labels[4] = '1e15'
    #axwnq2.set_xticklabels(labels, fontsize = 20)

    #axwnq2.tick_params(labelsize=10)
    pl.xticks(rotation=0)

    axwnq2.set_yscale("log", nonposy='clip')
    # pl.ylim([0.01, max(dfwnq2['100'] + dfwnq2['1000'] + dfwnq2['10000'])])
    pl.ylim([0.01,3000])

    for tick in axwnq2.xaxis.get_major_ticks():
        tick.label.set_fontsize(24) 

    for tick in axwnq2.yaxis.get_major_ticks():
        tick.label.set_fontsize(28) 

    # second x-axis
    # ax2 = axwnq2.twiny()
    # ax2.set_xlabel("Datasize",fontsize=25)
    # ax2.xaxis.labelpad = 12
    # ax2.set_xlim(0, 60)
    # ax2.set_xticks([7, 18, 30, 42, 53])
    # ax2.set_xticklabels(['1K','10K','100K','1M','20M'], fontsize=25)

    # grid
    axwnq2.yaxis.grid(which='major',linewidth=3.0,linestyle=':')
    axwnq2.set_axisbelow(True)

    # second x-axis
    # ax2 = axwnq2.twiny()
    # ax2.xaxis.set_ticks_position('bottom') # set the position of the second x-axis to bottom
    # ax2.xaxis.set_label_position('bottom') # set the position of the second x-axis to bottom
    # ax2.spines['bottom'].set_position(('outward', 80))

    #ax2.set_xlabel("Query Result Size",fontsize=26)
    # ax2.xaxis.labelpad = 12
    # ax2.set_xlim(0, 60)
    # ax2.set_xticklabels(['46','5.4K','171K','3.8M'],fontsize=24)
    # ax2.set_xticks([8, 23, 38, 52])

    # ax2.set_frame_on(True)
    # ax2.patch.set_visible(False)
    # ax2.spines["bottom"].set_visible(True)

    # pl.show()
    pl.savefig(str(name) + '.pdf', bbox_inches='tight')
    pl.cla()



if __name__=="__main__":
    main()
