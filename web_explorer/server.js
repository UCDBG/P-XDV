// server.js

const express = require('express');
const { Client } = require('pg');
const { spawn } = require('child_process');
const fs = require('fs');

const app = express();
const port = 3000;


// Setup PostgreSQL client
const client = new Client({
    host: "localhost",
    user: "postgres",
    port: 5500,
    password: "rootUser",
    database: "postgres"
});

// Connect to the PostgreSQL server
client.connect();

// Define route for handling requests to fetch owned table schema
app.get('/owned-table-schema', async (req, res) => {
    try {
        // Fetch owned table schema from the database
        const ownedQuery = `
            SELECT table_schema, table_name, string_agg(column_name, ', ') as columns
            FROM INFORMATION_SCHEMA.COLUMNS
            WHERE table_schema = 'owned'
            GROUP BY table_schema, table_name
            ORDER BY table_name`;
        const ownedResult = await client.query(ownedQuery);
        const ownedRows = ownedResult.rows;

        // Construct HTML markup for owned table schema
        let ownedTableHtml = '<h2>Owned Data Schema</h2>';
        ownedTableHtml += '<div class="table-box">'; // Add a container for the tables
        ownedRows.forEach(row => {
            ownedTableHtml += `
                <div class="table-container"> <!-- Wrap each table in a container div -->
                    <h3>${row.table_name} (${row.table_schema})</h3>
                    <div style="overflow-x:auto;">
                        <table>
                            <tbody>
                                <tr>
                                    <td>${row.columns}</td>
                                </tr>
                            </tbody>
                        </table>
                    </div>
                </div>
            `;
        });
        ownedTableHtml += '</div>'; // Close the container for the tables
        
        
        // Send the HTML markup as the response
        res.send(ownedTableHtml);
    
    } catch (error) {
        console.error('Error fetching owned table schema:', error);
        res.status(500).send('Internal Server Error');
    }
});

// Define route for handling requests to fetch shared table schema
app.get('/shared-table-schema', async (req, res) => {
    try {
        // Fetch shared table schema from the database
        const sharedQuery = `
            SELECT table_schema, table_name, string_agg(column_name, ', ') as columns
            FROM INFORMATION_SCHEMA.COLUMNS
            WHERE table_schema = 'shared'
            GROUP BY table_schema, table_name
            ORDER BY table_name`;
        const sharedResult = await client.query(sharedQuery);
        const sharedRows = sharedResult.rows;

        // Construct HTML markup for owned table schema
        let sharedTableHtml = '<h2>Shared Data Schema</h2>';
        sharedTableHtml += '<div class="table-box">'; // Add a container for the tables
        sharedRows.forEach(row => {
            sharedTableHtml += `
                <div class="table-container"> <!-- Wrap each table in a container div -->
                    <h3>${row.table_name} (${row.table_schema})</h3>
                    <div style="overflow-x:auto;">
                        <table>
                            <tbody>
                                <tr>
                                    <td>${row.columns}</td>
                                </tr>
                            </tbody>
                        </table>
                    </div>
                </div>
            `;
        });
        sharedTableHtml += '</div>'; // Close the container for the tables

        // Send the HTML markup as the response
        res.send(sharedTableHtml);
    } catch (error) {
        console.error('Error fetching shared table schema:', error);
        res.status(500).send('Internal Server Error');
    }
});


app.get('/generateGraphIG', (req, res) => {
    const pythonProcess = spawn('python3', ['graph.py']);
  
    let output = '';
    
    pythonProcess.stdout.on('data', (data) => {
      output += data.toString();
    });
  
    pythonProcess.stderr.on('data', (data) => {
      console.error(`stderr: ${data}`);
    });
  
    pythonProcess.on('close', (code) => {
      console.log(`child process exited with code ${code}`);
     
      if (code === 0) {
       
          // If the Python script executes successfully, serve the graph image
          res.sendFile(__dirname + '/public/output_plot.png');
        } else {
          res.status(500).send('Error generating graph.');
        }
        });
  });


app.get('/generateGraphIGEXPL', (req, res) => {
    const pythonProcess = spawn('python3', ['graphexpl.py']);
  
    let output = '';
    
    pythonProcess.stdout.on('data', (data) => {
      output += data.toString();
    });
  
    pythonProcess.stderr.on('data', (data) => {
      console.error(`stderr: ${data}`);
    });
  
    pythonProcess.on('close', (code) => {
      console.log(`child process exited with code ${code}`);
     
      if (code === 0) {
       
          // If the Python script executes successfully, serve the graph image
          res.sendFile(__dirname + '/public/output_plotexpl.png');
        } else {
          res.status(500).send('Error generating graph.');
        }
        });
  });


app.get('/', async (req, res) => {
    var responseHtml = fs.readFileSync('./index.html', { encoding: 'utf8', flag: 'r' });
    // var responseHtml;
    // fs.readFile('./Index.html', 'utf8', function read(err, data) {
    //     if (err) {
    //         throw err;
    //     }
    //     responseHtml = data;
    //     console.log(responseHtml);
    // });

    const action = req.query.action;
    // const scriptPath = '/Users/shek21/ResearchApps/gprom-ig/scripts/eig_run.sh';
    const scriptPath = '/Users/margiamin/Documents/gprom_IG/scripts/eig_run.sh';

    try {
        if (action === 'query') {
            // SQL Query Execution
            const query = req.query.query; //|| 'SELECT * FROM shared';
            const result = await client.query(query);
            const rows = result.rows;
             // Start of the table
            let tableHtml = '<h2>Query Result</h2>';
    
            if (rows.length > 0) {
        // Table with headers
                tableHtml += '<table border="1"><thead><tr>';

        // Dynamically generate column headers based on the first row's keys
                Object.keys(rows[0]).forEach(column => {
                    tableHtml += `<th>${column}</th>`;
              });

             tableHtml += '</tr></thead><tbody>';

        // Populate the table rows
        rows.forEach(row => {
            tableHtml += '<tr>';
            Object.values(row).forEach(value => {
                tableHtml += `<td>${value}</td>`; // Populate table data
            });
            tableHtml += '</tr>';
        });

        tableHtml += '</tbody></table>';
    } else {
        // No results found
        tableHtml += '<p>No results found.</p>';
    }

    // Append the table HTML to the response
    responseHtml += tableHtml;
}
            // responseHtml += `
            //     <h2>Query Result</h2>
            //     <ul>
            //         ${rows.map(row => `<li>${JSON.stringify(row)}</li>`).join('')}
            //     </ul>
            // `;
        else if (action === 'IGscript') {
            // External Script Execution
            const query = req.query.query;
            // const IGscriptPath = '/Users/shek21/ResearchApps/gprom-ig/scripts/eig_run.sh';
            const IGscriptProcess = spawn(scriptPath, ['0', `IG OF(${query});`]);
            
            let IGscriptOutput = '';
            for await (const chunk of IGscriptProcess.stdout) {
                IGscriptOutput += chunk;
            }

            let errorCode = await new Promise((resolve) => {
                IGscriptProcess.on('close', resolve);
            });

            if (errorCode) {
                IGscriptOutput += '\nError executing script.';
            }

            // Write to a CSV file
            fs.writeFile('output.csv', IGscriptOutput, (err) => {
                  if (err) {
                    console.error('Error writing CSV file:', err);
                    responseHtml += '<p>Error writing CSV file.</p>';
                    } else {
                    console.log('CSV file has been saved.');
            // // Read the CSV file and calculate the sum of "Total_IG" column
            // const csvData = fs.readFileSync('output.csv', 'utf8');
            // const rows = csvData.split('\n').map(row => row.split(',')); // Assuming ',' is the separator

            // let totalIGSum = 0;
            // for (let i = 1; i < rows.length; i++) { // Start from index 1 to skip header row
            //     totalIGSum += parseInt(rows[i][10]); // Assuming "Total_IG" is the 11th column (zero-based index)
            // }

            // //Append the sum to the response
            // responseHtml += `<p>Total sum of "Total_IG": ${totalIGSum}</p>`;

            // responseHtml += `
            //     <script>
            //     window.onload = function() {
            //         fetchOwnedTableSchema();
            //         fetchSharedTableSchema();
            //         showTrend();
            //     };
            //     </script>
            //     <h2>IG Result</h2>
            //     <pre>${IGscriptOutput}</pre>
            // `;

            // // Send the HTML response
            // res.send(responseHtml);
        }
    });
        //                         // Read the CSV file and calculate the sum of "Total_IG" column
        //             const csvData = fs.readFileSync('output.csv', 'utf8');
        //             const rows = csvData.split('\n').map(row => row.split(',')); // Assuming ',' is the separator

        //     let totalIGSum = 0;
        //     for (let i = 1; i < rows.length; i++) { // Start from index 1 to skip header row
        //         totalIGSum += parseInt(rows[i][17]); // Assuming "Total_IG" is the 17th column (zero-based index) insted last column
        //     }

        //     // Append the sum to the response
        //     responseHtml += `<p>Total sum of "Total_IG": ${totalIGSum}</p>`;
        // }

                    

                //     // Read the CSV file
                //     fs.readFile('./output.csv', 'utf8', (err, data) => {
                //         if (err) {
                //             console.error('Error reading CSV file:', err);
                //             responseHtml += '<p>Error reading CSV file.</p>';
                //         } else {
                //             // Parse CSV data
                //             const rows = data.split('\n').map(row => row.split(','));
                            
                //             // Extract the 41st column (assuming zero-based index)
                //             const column41 = rows.map(row => row[40]); // Assuming zero-based index
                            
                //             // Display the 41st column in the HTML response
                //             responseHtml += `<h2>41st Column of Output CSV</h2><pre>${column41.join('\n')}</pre>`;
                //             res.send(responseHtml);
                    
                //     }
                // });

            responseHtml += `
                <script>
                window.onload = function() {
                    fetchOwnedTableSchema();
                    fetchSharedTableSchema();
                    showTrend();
                };
                </script>
                <div id="igResultContainer" style="text-align: center; padding-left: 50px;">
                <h2 style="text-align: center; padding-left: 10px;">IG Result</h2> <!-- Add color: blue; -->
                <div style="padding-left: 10px;"> <!-- Center the container and align content to the left -->
                <pre>${IGscriptOutput}</pre>
                 </div>
                 </div>
            `;
    }
        
        else if (action === 'EXPLscript') {
            // External Script Execution
            const query = req.query.query;
            console.log(query);
            // console.log(req.query);
            // const scriptPath = '/Users/margiamin/Documents/gprom_IG/scripts/eig_run.sh';

            const topK = req.query['topk'];
            console.log(req.query['topk']);

         //  let topKMessage = ''; // Message to inform the user about the topK value used

            // if (!topK) {
            //     topK = '10'; // Default value if topK is not provided
            //     topKMessage = 'Notice: topK was not provided. Using a default value of 10.';
            // }

            let scriptProcess;

            if(topK == '') {
                scriptProcess = spawn(scriptPath, ['0', `IGEXPL TOP 10 OF(${query});`]);
            } else {
                scriptProcess = spawn(scriptPath, ['0', `IGEXPL TOP ${topK} OF(${query});`]);
            }
            
            let scriptOutput = '';
            for await (const chunk of scriptProcess.stdout) {
                scriptOutput += chunk;
            }

            let errorCode = await new Promise((resolve) => {
                scriptProcess.on('close', resolve);
            });

            if (errorCode) {
                scriptOutput += '\nError executing script.';
            }    
             // Write to a CSV file
             fs.writeFile('outputexpl.csv', scriptOutput, (err) => {
                if (err) {
                  console.error('Error writing CSV file:', err);
                  responseHtml += '<p>Error writing CSV file.</p>';
                  } else {
                  console.log('CSV file has been saved.');
                }
            });
    
      //         

            // // Include the topKMessage in the response HTML if it's not empty
            // if (topKMessage) {
            //     responseHtml += `<p>${topKMessage}</p>`;
            // }

            responseHtml += `
                <script>
                window.onload = function() {
                    fetchOwnedTableSchema();
                    fetchSharedTableSchema();
                    showTrendExpl();
                };
                </script>
                <div id="igResultContainer" style="text-align: center; padding-left: 50px;">
                <h2 style="text-align: center; padding-left: 10px;">Top-K Explanations</h2>
                <div style="padding-left: 10px;">
                <pre>${scriptOutput}</pre>
                </div>
                </div>
            `;
        }

    } catch (error) {
        console.error(error.message);
        responseHtml += `
            <p>Error performing the requested operation.</p>
        `;
        res.status(500).send(`Internal Server Error: ${error.message}`);
    }

    responseHtml += `
            </body>
        </html>
    `;

    res.send(responseHtml);
});

// Route to handle the button click and execute the Python script

// Middleware for serving static files
app.use(express.static('public'));

app.listen(port, () => {
    console.log(`Server running on http://localhost:${port}`);
});
