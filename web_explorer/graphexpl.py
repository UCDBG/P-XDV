import pandas as pd
import matplotlib.pyplot as plt

def generate_multiple_line_graph(csv_file_path, output_image_path, start_column_name, end_column_name):
    try:
        data = pd.read_csv(csv_file_path, sep='|')
        print(data.columns)
        
        # Ensure column indices are within bounds
        #max_col_index = len(data.columns) - 1
        #start_col_index = min(5, max_col_index)  # 8th column, z3ero-indexed
        #end_col_index = min(8, max_col_index)  # 15th column, inclusive
# Find the index of the start column name and the end column name
        start_col_index = data.columns.get_loc(start_column_name)
        end_col_index = data.columns.get_loc(end_column_name)
        # Slice the column names based on the indices
        column_names = data.columns[start_col_index:end_col_index + 1]

        # Adjust column range if out-of-bounds
        #column_indices = range(start_col_index, end_col_index + 1)
        #column_names = [data.columns[i] for i in column_indices if i <= max_col_index]
        
        x_values = range(1, len(data) + 1)
        
        for col_name in column_names:
            plt.plot(x_values, data[col_name], label=col_name)
        
        plt.xlabel("Patterns (row ID)", fontsize=29)  # Increase font size of xlabel
        plt.ylabel("Measured Metrics", fontsize=29)  # Increase font size of ylabel
        plt.title("IG Trends", fontsize=32)  # Increase font size of title
        
        plt.legend(fontsize=26)
            # Increase the font size of tick labels on both axes
        plt.xticks(fontsize=21)
        plt.yticks(fontsize=21)
        plt.xticks(x_values)  # Adjust as needed for visibility
        
          # Increase the figure size to stretch the plot
        plt.gcf().set_size_inches(16, 9)  # Adjust the width and height as needed

        plt.tight_layout(pad=3.0)  # Adjust subplot parameters to give specified padding


        plt.savefig(output_image_path)
        plt.close()  # Close the plot to prevent it from being displayed
        #plt.show()
    
    except FileNotFoundError:
        print("File not found. Please provide a valid file path.")
    except Exception as e:
        print("An error occurred:", str(e))

if __name__ == "__main__":
    csv_file_path = "./outputexpl.csv" 
    output_image_path = "./public/output_plotexpl.png"  # Ensure this is the correct path to your CSV file
    start_column_name = " pattern_IG "  # Specify the name of the starting column
    end_column_name = " f_score            "  # Specify the name of the ending column
    generate_multiple_line_graph(csv_file_path, output_image_path, start_column_name, end_column_name)
