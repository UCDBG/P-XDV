-- HAMMING FUNCTIONS IMPORTANT
-- hammingxor
 CREATE OR REPLACE FUNCTION public.hammingxor(value1 text, value2 text)
  RETURNS text                                                         
  LANGUAGE plpgsql                                                     
 AS $function$                                                         
 declare                                                               
 hamming text;                                                         
 begin                                                                 
 hamming = value1::bit(10) # value2::bit(10);                          
 return hamming;                                                       
 end;                                                                  
 $function$          

--hammingxorvalue
CREATE OR REPLACE FUNCTION public.hammingxorvalue(value1 text)
  RETURNS integer                                             
  LANGUAGE plpgsql                                            
 AS $function$                                                
 declare                                                      
 hamming int;                                                 
 begin                                                        
 hamming = length(replace(value1,'0',''));                    
 return hamming;                                              
 end;                                                         
 $function$                                                   

-- Table: public.owned
-- DROP TABLE IF EXISTS public.owned;
CREATE TABLE IF NOT EXISTS public.owned
(
    county character varying COLLATE pg_catalog."default",
    year integer,
    dayswaqi integer,
    maqi integer
)

TABLESPACE pg_default;

ALTER TABLE IF EXISTS public.owned
    OWNER to postgres;

-- Table: public.shared
-- DROP TABLE IF EXISTS public.shared;
CREATE TABLE IF NOT EXISTS public.shared
(
    county character varying COLLATE pg_catalog."default",
    year integer,
    gdays integer,
    maqi integer
)

TABLESPACE pg_default;

ALTER TABLE IF EXISTS public.shared
    OWNER to postgres;

-- Cancer full table
CREATE TABLE cancer
(
    ClumpThickness integer,
    UniformityofCellSize integer,
    UniformityofCellShape integer,
    MarginalAdhesion integer,
	  SingleEpithelialCellSize integer,
	  BareNuclei integer,
	  BlandChromatin integer,
	  NormalNucleoli integer,
	  Mitoses integer,
	  Class integer
)

-- Adding pid to cancer table i.e just a number from 1 to n
ALTER TABLE cancer
ADD COLUMN pid integer;

WITH numbered AS (
  SELECT ctid, row_number() OVER () AS rn
  FROM cancer
)
UPDATE cancer
SET pid = numbered.rn
FROM numbered
WHERE cancer.ctid = numbered.ctid;

-- Creating cancer o1 from cancer table, if uniformityofcellsize > 7 then risk level 1 otherwise 0
CREATE TABLE cancero1 AS
SELECT 
  pid,
  "uniformityofcellsize",
  "uniformityofcellshape",
  CASE 
    WHEN "uniformityofcellsize" > 7 THEN 1
    ELSE 0
  END AS risklevel
FROM cancer;

-- Creating cancer s1
CREATE TABLE cancers1 AS
SELECT 
  pid,
  "clumpthickness",
  "uniformityofcellsize",
  class
FROM cancer;

-- Creating cancer s2
CREATE TABLE cancers2 AS
SELECT 
  pid,
  "clumpthickness",
  "mitoses",
  class
FROM cancer;

-- OPTIONAL (CHANGING THE DATATYPE OF O1 S1 AND S2 FROM INTEGER TO NUMERIC IF NEEDED)
-- cancero1
ALTER TABLE cancero1
ALTER COLUMN pid TYPE numeric USING pid::numeric,
ALTER COLUMN "uniformityofcellsize" TYPE numeric USING "uniformityofcellsize"::numeric,
ALTER COLUMN "uniformityofcellshape" TYPE numeric USING "uniformityofcellshape"::numeric,
ALTER COLUMN risklevel TYPE numeric USING risklevel::numeric;
-- cancers1
ALTER TABLE cancers1
ALTER COLUMN pid TYPE numeric USING pid::numeric,
ALTER COLUMN "uniformityofcellsize" TYPE numeric USING "uniformityofcellsize"::numeric,
ALTER COLUMN "clumpthickness" TYPE numeric USING "clumpthickness"::numeric,
ALTER COLUMN class TYPE numeric USING class::numeric;
-- cancers2
ALTER TABLE cancers2
ALTER COLUMN pid TYPE numeric USING pid::numeric,
ALTER COLUMN "clumpthickness" TYPE numeric USING "clumpthickness"::numeric,
ALTER COLUMN "mitoses" TYPE numeric USING "mitoses"::numeric,
ALTER COLUMN class TYPE numeric USING class::numeric;



