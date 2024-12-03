import pandas as pd

# Function to calculate the sum of values in the 11th column
def calculate_sum_from_csv(filename):
    # Read CSV file into a DataFrame
    data = pd.read_csv(filename, sep='|')

    # Extract the 11th column and calculate the sum
    column_11 = data.iloc[:, 10]  # Assuming the 11th column is numeric (indexing starts from 0)
    total_sum = column_11.sum()

    return total_sum

# File path of the CSV file
csv_file_path = 'output.csv'

# Calculate the sum of values in the 11th column
total_sum = calculate_sum_from_csv(csv_file_path)

# Print the total sum
print("Sum of values in the 11th column:", total_sum)
