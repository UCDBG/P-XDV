const express = require('express')
const {Client} = require('pg')

const app = express();
const port = 3000;

const client = new Client({
    host: "localhost",
    user: "postgres",
    port: 5500,
    password: "rootUser",
    database: "postgres"
})

client.connect();

app.get('/', async (req, res) => {
    try {
        const query = req.query.query || 'SELECT * FROM shared';
        const result = await client.query(query);
        const rows = result.rows;
        res.send(`
            <html>
                <form action="/" method="GET">
                    <label for="queryInput">Enter SQL Query:</label>
                    <input type="text" id="queryInput" name="query" placeholder="Type your SQL query here">
                    <button type="submit">Run Query</button>
                </form>

                <h2>Query Result</h2>
                <ul>
                    ${rows.map(row => `<li>${JSON.stringify(row)}</li>`).join('')}
                </ul>
            </html>
        `);
    } catch (error) {
        console.error(error.message);
        res.status(500).send('Internal Server Error');
    }
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
