const express = require('express');
const { Client } = require('pg');
const { spawn } = require('child_process');

const app = express();
const port = 3000;

const client = new Client({
    host: "localhost",
    user: "postgres",
    port: 5500,
    password: "rootUser",
    database: "postgres"
});

client.connect();

app.get('/', async (req, res) => {
    try {
        const userQuery = req.query.query || 'SELECT * FROM shared';

        // Use parameterized queries to prevent SQL injection
        const queryText = {
            text: userQuery,
        };

        const result = await client.query(queryText);
        const rows = result.rows;

        res.send(`
            <html>
                <body>
                    <form action="/" method="GET">
                        <label for="queryInput">Enter SQL Query:</label>
                        <input type="text" id="queryInput" name="query" placeholder="Type your SQL query here" value="${userQuery}">
                        <button type="submit">Run Query</button>
                    </form>

                    <h2>Query Result</h2>
                    <ul>
                        ${rows.map(row => `<li>${JSON.stringify(row)}</li>`).join('')}
                    </ul>
                </body>
            </html>
        `);
    } catch (error) {
        console.error(error.message);
        res.status(500).send('Internal Server Error');
    }
});

app.get('/runScript', (req, res) => {
    const scriptPath = './gprom_IG/scripts/eig_run.sh';
    const scriptArguments = ['3', 'IG OF(Select * from owned o JOIN shared s ON(o.county = s.county));'];
    //const scriptArgs = ['3', 'IG', `OF(${tempText})`];

    const scriptProcess = spawn(scriptPath, scriptArguments);

    scriptProcess.stdout.on('data', (data) => {
        console.log(`Script output: ${data}`);
        res.send(`Script output: ${data}`);
    });

    scriptProcess.stderr.on('data', (data) => {
        console.error(`Script error: ${data}`);
        res.status(500).send('Internal Server Error');
    });

    scriptProcess.on('close', (code) => {
        console.log(`Script process exited with code ${code}`);
    });
});

app.listen(port, () => {
    console.log(`Server is running on http://localhost:${port}`);
});
