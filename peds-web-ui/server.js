// server.js
const express = require('express');
const { Client } = require('pg');
const { spawn } = require('child_process');
const fs = require('fs');
const csvParser = require('csv-parser');
const bodyParser = require('body-parser');
const path = require('path');
const { table } = require('console');

const app = express();
const port = 3000;

// Setup PostgreSQL client
// const client = new Client({
//     host: "localhost",
//     user: "postgres",
//     port: 5500,
//     password: "rootUser",
//     database: "postgres"
// });

const client = new Client({
    host: "localhost",
    user: "postgres",
    port: 5432,
    password: "shemon90",
    database: "postgres"
});

// Connect to the PostgreSQL server
client.connect();
console.log("connection successfull");

// Serve static files (like index.html, CSS, and JS)
app.use(express.static(path.join(__dirname, 'public')));
// app.use(bodyParser.json());
// Increase the limit to 50MB (adjust as needed)
app.use(bodyParser.json({ limit: '50mb' }));
app.use(bodyParser.urlencoded({ limit: '50mb', extended: true })); 

// Check if a table exists
const checkTableExistsOwned = async (tableName) => {
    console.log("inside owned checkTableExists()");
    const query = `
        SELECT EXISTS (
            SELECT FROM information_schema.tables 
            WHERE table_name = $1
        )`;
    const result = await client.query(query, [tableName]);
    return result.rows[0].exists;
};

const checkTableExistsShared = async (tableName) => {
    console.log("inside shared checkTableExists()");
    const query = `
        SELECT EXISTS (
            SELECT FROM information_schema.tables 
            WHERE table_name = $1
        )`;
    const result = await client.query(query, [tableName]);
    return result.rows[0].exists;
};

app.listen(port, () => {
    console.log(`Server running at http://localhost:${port}`);
});

//upload owned tables
app.post('/uploadOwned', async (req, res) => {
    try {
        console.log("inside /uploadOwned");
        const csvData = req.body.csvData;
        const tableName = req.body.tableName || 'default_table';
        console.log("table name: ", tableName);

        const rows = csvData.split('\n')
        .map(row => row.split(',').map(value => value.trim()))
        .filter(row => row.length > 0 && row.some(value => value !== ''));

        if (rows.length < 2) {
            return res.status(400).send('CSV must have at least one data row');
        }

        // Extract column names from the first row of the CSV
        const columnNames = rows.shift(); // Remove the first row and use it as column names

        // Ensure column names are sanitized for SQL compatibility
        const sanitizedColumnNames = columnNames.map(col => col.replace(/[^a-zA-Z0-9_]/g, '').toLowerCase());

        // Determine data types for each column based on the first few rows
        const sampleRows = rows.slice(0, Math.min(rows.length, 3)); // Use up to 3 rows for sampling
        console.log("top 3 sample rows", sampleRows);
        const dataTypes = columnNames.map((_, colIndex) => {
            for (const row of sampleRows) {
                const value = row[colIndex];
                if (!isNaN(value) && value !== '') {
                    // Check if value is a number
                    continue; // Assume number unless a string is found
                } else {
                    return 'character varying'; // Found a string, use character varying
                }
            }
            return 'integer'; // All sampled values are numbers
        });
        console.log('Determined data types:', dataTypes);

        // Check if the table exists
        const tableExists = await checkTableExistsOwned(tableName);
        console.log("table Exists: ", tableExists);
        if (tableExists) {
            res.status(409).send({ message: 'Table already exists. Please provide a different table name.' });
            return;
        }

        // Create table dynamically
        const createTableQuery = `
            CREATE TABLE ${tableName} (
                ${columnNames.map((col, index) => `${col} ${dataTypes[index]}`).join(', ')}
            )
        `;

        await client.query(createTableQuery);

        // Generate INSERT query dynamically
        const insertQuery = `
        INSERT INTO ${tableName} (${sanitizedColumnNames.join(', ')})
        VALUES (${sanitizedColumnNames.map((_, index) => `$${index + 1}`).join(', ')})
        `;

        // Insert data into the table
        for (let i = 0; i < rows.length; i++) {
            if (rows[i].length !== sanitizedColumnNames.length) {
                console.warn(`Skipping row ${i + 1} due to mismatched column count:`, rows[i]);
                continue;
            }
            try {
                await client.query(insertQuery, rows[i]);
            } catch (error) {
                console.error(`Error inserting row ${i + 1}:`, error);
            }
        }

        console.log("insert query completed", insertQuery);
        res.status(200).send('CSV data uploaded shared data successfully');

    } catch (error) {
        console.error(error);
        res.status(500).send('An error occurred while uploading owned data.');
    }
});

//upload shared tables
app.post('/uploadShared', async (req, res) => {
    try {
        console.log("inside /uploadShared");
        const csvData = req.body.csvData;
        const tableName = req.body.tableName || 'default_table';
        console.log("table name: ", tableName);

        const rows = csvData.split('\n')
        .map(row => row.split(',').map(value => value.trim()))
        .filter(row => row.length > 0 && row.some(value => value !== ''));

        if (rows.length < 2) {
            return res.status(400).send('CSV must have at least one data row');
        }

        // Extract column names from the first row of the CSV
        const columnNames = rows.shift(); // Remove the first row and use it as column names

        // Ensure column names are sanitized for SQL compatibility
        const sanitizedColumnNames = columnNames.map(col => col.replace(/[^a-zA-Z0-9_]/g, '').toLowerCase());

        // Determine data types for each column based on the first few rows
        const sampleRows = rows.slice(0, Math.min(rows.length, 3)); // Use up to 3 rows for sampling
        console.log("top 3 sample rows", sampleRows);
        const dataTypes = columnNames.map((_, colIndex) => {
            for (const row of sampleRows) {
                const value = row[colIndex];
                if (!isNaN(value) && value !== '') {
                    // Check if value is a number
                    continue; // Assume number unless a string is found
                } else {
                    return 'character varying'; // Found a string, use character varying
                }
            }
            return 'integer'; // All sampled values are numbers
        });
        console.log('Determined data types:', dataTypes);

        // Check if the table exists
        const tableExists = await checkTableExistsShared(tableName);
        console.log("table Exists: ", tableExists);
        if (tableExists) {
            res.status(409).send({ message: 'Table already exists. Please provide a different table name.' });
            return;
        }

        // Create table dynamically
        const createTableQuery = `
            CREATE TABLE ${tableName} (
                ${columnNames.map((col, index) => `${col} ${dataTypes[index]}`).join(', ')}
            )
        `;

        await client.query(createTableQuery);

        // Generate INSERT query dynamically
        const insertQuery = `
        INSERT INTO ${tableName} (${sanitizedColumnNames.join(', ')})
        VALUES (${sanitizedColumnNames.map((_, index) => `$${index + 1}`).join(', ')})
        `;

        // Insert data into the table
        for (let i = 0; i < rows.length; i++) {
            if (rows[i].length !== sanitizedColumnNames.length) {
                console.warn(`Skipping row ${i + 1} due to mismatched column count:`, rows[i]);
                continue;
            }
            try {
                await client.query(insertQuery, rows[i]);
            } catch (error) {
                console.error(`Error inserting row ${i + 1}:`, error);
            }
        }

        console.log("insert query completed", insertQuery);
        res.status(200).send('CSV data uploaded successfully in shared schema');

    } catch (error) {
        console.error(error);
        res.status(500).send('An error occurred while uploading shared data.');
    }
});

//route for schema owned display
app.get('/schemaOwned', async (req, res) => {
    try {
        // Fetch all owned tables
        const tablesQueryOwned = `
            SELECT table_name
            FROM information_schema.tables
            WHERE table_name LIKE '%_owned'
        `;
        const tablesResultOwned = await client.query(tablesQueryOwned);

        const tablesOwned = await Promise.all(
            tablesResultOwned.rows.map(async ({ table_name }) => {
                // Fetch column details for each table
                const columnsQuery = `
                    SELECT column_name, data_type
                    FROM information_schema.columns
                    WHERE table_name = $1
                `;
                const columnsResult = await client.query(columnsQuery, [table_name]);
                return {
                    table_name,
                    schema: columnsResult.rows,
                };
            })
        );

        res.status(200).json(tablesOwned);
    } catch (error) {
        console.error('Error fetching owned table schema:', error);
        res.status(500).send('Error fetching owned table schema');
    }
});

//route for schema shared display
app.get('/schemaShared', async (req, res) => {
    try {
        // Fetch all shared tables
        const tablesQueryShared = `
            SELECT table_name
            FROM information_schema.tables
            WHERE table_name LIKE '%_shared'
        `;
        const tablesResultShared = await client.query(tablesQueryShared);

        const tablesShared = await Promise.all(
            tablesResultShared.rows.map(async ({ table_name }) => {
                // Fetch column details for each table
                const columnsQuery = `
                    SELECT column_name, data_type
                    FROM information_schema.columns
                    WHERE table_name = $1
                `;
                const columnsResult = await client.query(columnsQuery, [table_name]);
                return {
                    table_name,
                    schema: columnsResult.rows,
                };
            })
        );
        
        res.status(200).json(tablesShared);
    } catch (error) {
        console.error('Error fetching shared table schema:', error);
        res.status(500).send('Error fetching shared table schema');
    }
});

app.post('/execute-query', async (req, res) => {
        const { query } = req.body;
        const scriptPath = '/Users/shemraw/Downloads/gprom/scripts/eig_run.sh';

        if (!query) {
            return res.status(400).json({ error: 'No query provided' });
        }
        const scriptProcess = spawn(scriptPath, ['0', `(${query});`]);
        console.log("new script spawn", scriptProcess);
        let output = '';
        let errorOutput = '';

        // Capture standard output
        scriptProcess.stdout.on('data', (data) => {
            output += data.toString();
        });

        // Capture error output
        scriptProcess.stderr.on('data', (data) => {
            errorOutput += data.toString();
        });

        // Handle process close
        scriptProcess.on('close', (code) => {
            if (code === 0) {
                res.status(200).json({ message: 'Script executed successfully', output });
            } else {
                res.status(500).json({ error: errorOutput || 'An error occurred while running the script' });
            }
        });

        // Handle errors
        scriptProcess.on('error', (err) => {
            console.error('Failed to start script:', err);
            res.status(500).json({ error: 'Failed to start script' });
        });
});

// const scriptPath = '/Users/shek21/ResearchApps/gprom-ig/scripts/eig_run.sh';
// const scriptPath = '/Users/margiamin/Documents/gprom_IG/scripts/eig_run.sh';
// const scriptPath = '/Users/shemraw/Downloads/gprom/scripts/eig_run.sh';
app.post('/estimate-price', (req, res) => {
    console.log("inside /estimate-price");
    const { query } = req.body;
    const scriptPath = '/Users/shemraw/Downloads/gprom/scripts/eig_run.sh';
    if (!query) {
        return res.status(400).json({ error: 'No query provided' });
    }

    // Command and arguments
    // const script = scriptPath + `"IG OF (${query});"`;
    // console.log(`Running script: ${script}`);

    // Execute the script
    // const scriptProcess = spawn(script, ['0', `"IG OF (${query});"]);
    // ./scripts/eig_run.sh 3 “IG OF (SELECT * from owned o FULL OUTER JOIN shared s ON (o.county = s.county AND o.year = s.year));”
    const scriptProcess = spawn(scriptPath, ['0', `IG OF(${query});`]);
    let output = '';
    let errorOutput = '';

    // Capture standard output
    scriptProcess.stdout.on('data', (data) => {
        output += data.toString();
    });

    // Capture error output
    scriptProcess.stderr.on('data', (data) => {
        errorOutput += data.toString();
    });

    // Handle process close
    scriptProcess.on('close', (code) => {
        if (code === 0) {
            res.status(200).json({ message: 'Script executed successfully', output });
        } else {
            res.status(500).json({ error: errorOutput || 'An error occurred while running the script' });
        }
    });

    // Handle errors
    scriptProcess.on('error', (err) => {
        console.error('Failed to start script:', err);
        res.status(500).json({ error: 'Failed to start script' });
    });
});

app.post('/expl-peds', (req, res) => {
    console.log("inside /expl-peds");
    const { query,kInput } = req.body;
    const scriptPath = '/Users/shemraw/Downloads/gprom/scripts/eig_run.sh';
    if (!query) {
        return res.status(400).json({ error: 'No query provided' });
    }

    // Execute the script
    console.log("kInput from server.js", kInput);
    const scriptProcess = spawn(scriptPath, ['0', `IGEXPL TOP ${kInput} OF(${query});`]);
    console.log("new script spawn", scriptProcess);
    let output = '';
    let errorOutput = '';

    // Capture standard output
    scriptProcess.stdout.on('data', (data) => {
        output += data.toString();
    });

    // Capture error output
    scriptProcess.stderr.on('data', (data) => {
        errorOutput += data.toString();
    });

    // Handle process close
    scriptProcess.on('close', (code) => {
        if (code === 0) {
            res.status(200).json({ message: 'Script executed successfully', output });
        } else {
            res.status(500).json({ error: errorOutput || 'An error occurred while running the script' });
        }
    });

    // Handle errors
    scriptProcess.on('error', (err) => {
        console.error('Failed to start script:', err);
        res.status(500).json({ error: 'Failed to start script' });
    });
});






// app.get('/generateGraphIG', (req, res) => {
//     const pythonProcess = spawn('python3', ['graph.py']);
  
//     let output = '';
    
//     pythonProcess.stdout.on('data', (data) => {
//       output += data.toString();
//     });
  
//     pythonProcess.stderr.on('data', (data) => {
//       console.error(`stderr: ${data}`);
//     });
  
//     pythonProcess.on('close', (code) => {
//       console.log(`child process exited with code ${code}`);
     
//       if (code === 0) {
       
//           // If the Python script executes successfully, serve the graph image
//           res.sendFile(__dirname + '/public/output_plot.png');
//         } else {
//           res.status(500).send('Error generating graph.');
//         }
//         });
//   });


// app.get('/generateGraphIGEXPL', (req, res) => {
//     const pythonProcess = spawn('python3', ['graphexpl.py']);
  
//     let output = '';
    
//     pythonProcess.stdout.on('data', (data) => {
//       output += data.toString();
//     });
  
//     pythonProcess.stderr.on('data', (data) => {
//       console.error(`stderr: ${data}`);
//     });
  
//     pythonProcess.on('close', (code) => {
//       console.log(`child process exited with code ${code}`);
     
//       if (code === 0) {
       
//           // If the Python script executes successfully, serve the graph image
//           res.sendFile(__dirname + '/public/output_plotexpl.png');
//         } else {
//           res.status(500).send('Error generating graph.');
//         }
//         });
//   });


// app.get('/', async (req, res) => {
//     var responseHtml = fs.readFileSync('./index.html', { encoding: 'utf8', flag: 'r' });
//     // var responseHtml;
//     // fs.readFile('./Index.html', 'utf8', function read(err, data) {
//     //     if (err) {
//     //         throw err;
//     //     }
//     //     responseHtml = data;
//     //     console.log(responseHtml);
//     // });

//     const action = req.query.action;
//     // const scriptPath = '/Users/shek21/ResearchApps/gprom-ig/scripts/eig_run.sh';
//     // const scriptPath = '/Users/margiamin/Documents/gprom_IG/scripts/eig_run.sh';
//     const scriptPath = '/Users/shemraw/Downloads/gprom/scripts/eig_run.sh';

//     try {
//         if (action === 'query') {
//             // SQL Query Execution
//             const query = req.query.query; //|| 'SELECT * FROM shared';
//             const result = await client.query(query);
//             const rows = result.rows;
//              // Start of the table
//             let tableHtml = '<h2>Query Result</h2>';
    
//             if (rows.length > 0) {
//         // Table with headers
//                 tableHtml += '<table border="1"><thead><tr>';

//         // Dynamically generate column headers based on the first row's keys
//                 Object.keys(rows[0]).forEach(column => {
//                     tableHtml += `<th>${column}</th>`;
//               });

//              tableHtml += '</tr></thead><tbody>';

//         // Populate the table rows
//         rows.forEach(row => {
//             tableHtml += '<tr>';
//             Object.values(row).forEach(value => {
//                 tableHtml += `<td>${value}</td>`; // Populate table data
//             });
//             tableHtml += '</tr>';
//         });

//         tableHtml += '</tbody></table>';
//     } else {
//         // No results found
//         tableHtml += '<p>No results found.</p>';
//     }

//     // Append the table HTML to the response
//     responseHtml += tableHtml;
// }
//             // responseHtml += `
//             //     <h2>Query Result</h2>
//             //     <ul>
//             //         ${rows.map(row => `<li>${JSON.stringify(row)}</li>`).join('')}
//             //     </ul>
//             // `;
//         else if (action === 'IGscript') {
//             // External Script Execution
//             const query = req.query.query;
//             // const IGscriptPath = '/Users/shek21/ResearchApps/gprom-ig/scripts/eig_run.sh';
//             const IGscriptProcess = spawn(scriptPath, ['0', `IG OF(${query});`]);
            
//             let IGscriptOutput = '';
//             for await (const chunk of IGscriptProcess.stdout) {
//                 IGscriptOutput += chunk;
//             }

//             let errorCode = await new Promise((resolve) => {
//                 IGscriptProcess.on('close', resolve);
//             });

//             if (errorCode) {
//                 IGscriptOutput += '\nError executing script.';
//             }

//             // Write to a CSV file
//             fs.writeFile('output.csv', IGscriptOutput, (err) => {
//                   if (err) {
//                     console.error('Error writing CSV file:', err);
//                     responseHtml += '<p>Error writing CSV file.</p>';
//                     } else {
//                     console.log('CSV file has been saved.');
//             // // Read the CSV file and calculate the sum of "Total_IG" column
//             // const csvData = fs.readFileSync('output.csv', 'utf8');
//             // const rows = csvData.split('\n').map(row => row.split(',')); // Assuming ',' is the separator

//             // let totalIGSum = 0;
//             // for (let i = 1; i < rows.length; i++) { // Start from index 1 to skip header row
//             //     totalIGSum += parseInt(rows[i][10]); // Assuming "Total_IG" is the 11th column (zero-based index)
//             // }

//             // //Append the sum to the response
//             // responseHtml += `<p>Total sum of "Total_IG": ${totalIGSum}</p>`;

//             // responseHtml += `
//             //     <script>
//             //     window.onload = function() {
//             //         fetchOwnedTableSchema();
//             //         fetchSharedTableSchema();
//             //         showTrend();
//             //     };
//             //     </script>
//             //     <h2>IG Result</h2>
//             //     <pre>${IGscriptOutput}</pre>
//             // `;

//             // // Send the HTML response
//             // res.send(responseHtml);
//         }
//     });
//         //                         // Read the CSV file and calculate the sum of "Total_IG" column
//         //             const csvData = fs.readFileSync('output.csv', 'utf8');
//         //             const rows = csvData.split('\n').map(row => row.split(',')); // Assuming ',' is the separator

//         //     let totalIGSum = 0;
//         //     for (let i = 1; i < rows.length; i++) { // Start from index 1 to skip header row
//         //         totalIGSum += parseInt(rows[i][17]); // Assuming "Total_IG" is the 17th column (zero-based index) insted last column
//         //     }

//         //     // Append the sum to the response
//         //     responseHtml += `<p>Total sum of "Total_IG": ${totalIGSum}</p>`;
//         // }

                    

//                 //     // Read the CSV file
//                 //     fs.readFile('./output.csv', 'utf8', (err, data) => {
//                 //         if (err) {
//                 //             console.error('Error reading CSV file:', err);
//                 //             responseHtml += '<p>Error reading CSV file.</p>';
//                 //         } else {
//                 //             // Parse CSV data
//                 //             const rows = data.split('\n').map(row => row.split(','));
                            
//                 //             // Extract the 41st column (assuming zero-based index)
//                 //             const column41 = rows.map(row => row[40]); // Assuming zero-based index
                            
//                 //             // Display the 41st column in the HTML response
//                 //             responseHtml += `<h2>41st Column of Output CSV</h2><pre>${column41.join('\n')}</pre>`;
//                 //             res.send(responseHtml);
                    
//                 //     }
//                 // });

//             responseHtml += `
//                 <script>
//                 window.onload = function() {
//                     fetchOwnedTableSchema();
//                     fetchSharedTableSchema();
//                     showTrend();
//                 };
//                 </script>
//                 <div id="igResultContainer" style="text-align: center; padding-left: 50px;">
//                 <h2 style="text-align: center; padding-left: 10px;">IG Result</h2> <!-- Add color: blue; -->
//                 <div style="padding-left: 10px;"> <!-- Center the container and align content to the left -->
//                 <pre>${IGscriptOutput}</pre>
//                  </div>
//                  </div>
//             `;
//     }
        
//         else if (action === 'EXPLscript') {
//             // External Script Execution
//             const query = req.query.query;
//             console.log(query);
//             // console.log(req.query);
//             // const scriptPath = '/Users/margiamin/Documents/gprom_IG/scripts/eig_run.sh';

//             const topK = req.query['topk'];
//             console.log(req.query['topk']);

//          //  let topKMessage = ''; // Message to inform the user about the topK value used

//             // if (!topK) {
//             //     topK = '10'; // Default value if topK is not provided
//             //     topKMessage = 'Notice: topK was not provided. Using a default value of 10.';
//             // }

//             let scriptProcess;

//             if(topK == '') {
//                 scriptProcess = spawn(scriptPath, ['0', `IGEXPL TOP 10 OF(${query});`]);
//             } else {
//                 scriptProcess = spawn(scriptPath, ['0', `IGEXPL TOP ${topK} OF(${query});`]);
//             }
            
//             let scriptOutput = '';
//             for await (const chunk of scriptProcess.stdout) {
//                 scriptOutput += chunk;
//             }

//             let errorCode = await new Promise((resolve) => {
//                 scriptProcess.on('close', resolve);
//             });

//             if (errorCode) {
//                 scriptOutput += '\nError executing script.';
//             }    
//              // Write to a CSV file
//              fs.writeFile('outputexpl.csv', scriptOutput, (err) => {
//                 if (err) {
//                   console.error('Error writing CSV file:', err);
//                   responseHtml += '<p>Error writing CSV file.</p>';
//                   } else {
//                   console.log('CSV file has been saved.');
//                 }
//             });
    
//       //         

//             // // Include the topKMessage in the response HTML if it's not empty
//             // if (topKMessage) {
//             //     responseHtml += `<p>${topKMessage}</p>`;
//             // }

//             responseHtml += `
//                 <script>
//                 window.onload = function() {
//                     fetchOwnedTableSchema();
//                     fetchSharedTableSchema();
//                     showTrendExpl();
//                 };
//                 </script>
//                 <div id="igResultContainer" style="text-align: center; padding-left: 50px;">
//                 <h2 style="text-align: center; padding-left: 10px;">Top-K Explanations</h2>
//                 <div style="padding-left: 10px;">
//                 <pre>${scriptOutput}</pre>
//                 </div>
//                 </div>
//             `;
//         }

//     } catch (error) {
//         console.error(error.message);
//         responseHtml += `
//             <p>Error performing the requested operation.</p>
//         `;
//         res.status(500).send(`Internal Server Error: ${error.message}`);
//     }

//     responseHtml += `
//             </body>
//         </html>
//     `;

//     res.send(responseHtml);
// });

// // Route to handle the button click and execute the Python script

// // Middleware for serving static files
// app.use(express.static('public'));

// app.listen(port, () => {
//     console.log(`Server running on http://localhost:${port}`);
// });
