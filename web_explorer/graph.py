import pandas as pd
import matplotlib.pyplot as plt

def generate_multiple_line_graph(csv_file_path, output_image_path, start_column_name, end_column_name):
    try:
        data = pd.read_csv(csv_file_path, sep='|')

    # Remove leading and trailing whitespaces from column names
        data.columns = data.columns.str.strip()

                # Find the index of the start column name and the end column name
        start_col_index = data.columns.get_loc(start_column_name)
        end_col_index = data.columns.get_loc(end_column_name)
        # Slice the column names based on the indices
        column_names = data.columns[start_col_index:end_col_index + 1]

        # Ensure column indices are within bounds
        #max_col_index = len(data.columns) - 1
        #start_col_index = min(5, max_col_index)  # 8th column, zero-indexed
        #end_col_index = min(9, max_col_index)  # 15th column, inclusive

        # Adjust column range if out-of-bounds
        #column_indices = range(start_col_index, end_col_index + 1)
        #column_names = [data.columns[i] for i in column_indices if i <= max_col_index]
        
        x_values = range(1, len(data) + 1)
        
        for col_name in column_names:
            plt.plot(x_values, data[col_name], label=col_name)
              # Calculate the total of values in the specified column
        #column_total = data[column_name].sum()

        plt.xlabel("Data points (row ID)", fontsize=29)  # Increase font size of xlabel
        plt.ylabel("New Information Obtained (IG)", fontsize=29)  # Increase font size of ylabel
        plt.title("IG Trends", fontsize=32)  # Increase font size of title
        
        plt.legend(fontsize=26)
        plt.xticks(fontsize=21)
        plt.yticks(fontsize=21)
        plt.xticks(x_values)  # Adjust as needed for visibility
        
         # Calculate the total of values in the last column
        last_column_total = data[end_column_name].sum()

           # Add a text annotation for the total of values in the specified column under the graph
        plt.text(0.5, -0.3, f"Estimate price: {last_column_total}", fontsize=36, transform=plt.gca().transAxes, ha='center')

          # Increase the figure size to stretch the plot
        plt.gcf().set_size_inches(16, 9)  # Adjust the width and height as needed
 # Add white space under the graph by adjusting the margins
       # plt.subplots_adjust(bottom=3)
  
        plt.tight_layout(pad=3.0)  # Adjust padding and spacing between subplots


        plt.savefig(output_image_path)
        plt.close()  # Close the plot to prevent it from being displayed
        #plt.show()
    
    except FileNotFoundError:
        print("File not found. Please provide a valid file path.")
    except Exception as e:
        print("An error occurred:", str(e))

if __name__ == "__main__":
    csv_file_path = "./output.csv" 
    output_image_path = "./public/output_plot.png"  # Ensure this is the correct path to your CSV file
   # column_name = "Total_IG"  # Specify the name of the column for which you want to calculate the total
    
    start_column_name = "IG_owned_county"  # Specify the name of the starting column
    end_column_name = "Total_IG"  # Specify the name of the ending column
    generate_multiple_line_graph(csv_file_path, output_image_path, start_column_name, end_column_name)
