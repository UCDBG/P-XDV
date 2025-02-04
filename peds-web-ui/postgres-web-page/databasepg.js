const express = require('express');
const {Client} = require('pg');
const path = require('path');

const app = express();
const port = 3000;

const client = new Client({
    host: "localhost",
    user: "postgres",
    port: 5432,
    password: "",
    database: "postgres"
})

client.connect();

app.get('/', async (req, res) => {
    try {
        let query = req.query.query;
        if(!query) {
            query = 'SELECT * FROM shared';
        }

        console.log("Request received.");
        // response.writeHead(200, {"Content-Type": "text/plain"});
        
        const subProcess = require('child_process');

        // const process = subProcess.spawn('ls', ['-al'])
        // process.on('exit', () => console.log('the ls command finished'))

        // // Let’s get the `ls -al` output
        // process.stdout.on('data', (data) => {
        //   console.log(`The stdout from create-react-app: ${data}`)
        // })

        // const scriptPath = './gprom_IG/scripts/eig_run.sh';
        // const scriptArguments = ['0 IG OF(Select * from owned o JOIN shared s ON(o.county = s.county));'];

        const igScript = 'IG OF(SELECT * FROM owned o JOIN shared s ON(o.county = s.county));';
        const scriptProcess = subProcess.spawn('../../gprom-ig/scripts/eig_run.sh', ['0', `${igScript}`]);

        scriptProcess.on('exit', () => console.log(`the EIG command finished`));

        scriptProcess.stdout.on('data', (data) => {
            console.log(`Script output: ${data}`);
            // res.send(`Script output: ${data}`);
        });

        // const result = await client.query(query);
        // const rows = result.rows;

        res.sendFile(path.join(__dirname + '/index.html'));

        client.query(query, (err, result, field) => {
    
            return Object.values(JSON.parse(JSON.stringify(result)));

        });
        // res.send(`
        //     <html>
        //         <body>
        //             <form action="/execute" method="post">
        //                 <label for="queryInput">Enter SQL Query:</label>
        //                 <input type="text" id="queryInput" name="query" placeholder="Type your SQL query here">
        //                 <button type="submit">Run Query</button>
        //             </form>
        //         </body>
        //     </html>
        //     <html>
        //         <h2>Query Result</h2>
        //         <ul>
        //             ${rows.map(row => `<li>${JSON.stringify(row)}</li>`).join('')}
        //         </ul>
        //     </html>
        // `);
    } catch (error) {
        console.error(error.message);
        res.status(500).send('Internal Server Error');
    }
});

// app.post('/execute', async (req, res) => {
//     const query = req.query.query;
//     const result = await client.query(query);
//     const rows = result.rows;

//     try {
//         if(result) {
//             // res.redirect('/');
//             res.json(result);
//             // ${rows.map(row => `<li>${JSON.stringify(row)}</li>`).join('')}
//         }        
//     } catch (error) {
//         console.error('Something went wrong', error.message);
//     }

// });


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
//code to print tabel in terminal by connnecting postgres.
// client.connect();

// client.query('select * from shared', (err, res)=>{
//     if(!err){
//         console.log(res.rows);
//     } else {
//         console.log(err.message);
//     }
//     client.end;
// })
