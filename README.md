# BallotVerification
Fourth part of the [*MoCa QR*](https://github.com/CamiloG/moca_qr) Voting System project.

Verifies that the selection made in [BallotSelection](https://github.com/CamiloG/BallotSelection) was the same as the one encrypted in the printed ballot.

## Files
1. **BallotVerification.java**: Main class of the program, where are all the logic and the methods to the configuration of the public information, and the reading and processing of both QR codes.

2. **GUILanterna.java**: Class that manages the Lanterna GUI environment, made to run on console-text-only devices. The recommended is to run this application in the less hardware necessary, so is very common to run this application on a Raspberry PI without graphic interface.

3. **AuthorityPublicKey.java**: Class for the creation of the object after the retrieving of the JSON from the Bulletin Board server.

## How to Use
* Download the .jar file [here](https://github.com/CamiloG/moca_qr/blob/master/Precinct_Apps/BallotVerification.jar?raw=true).
* Put the file ballotVerification.jar in the project folder.
* Execute ballotVerification.jar with `$ java -jar ballotVerification.jar`

### Configuration
* Make sure that you have access to the files of the public key and the list of candidates to configure this application.
* Select Configure Public Information'.
* Choose the public key file (/publicKeyN.key).
* Next, choose the candidates list (/candidates.xml).
* A remainder in the top of the window shows that we had already configure these necessary files.

### Verification Process
* Select 'Initialize Verification'.
* Next, the program asks for the voter to read with the code-reader the first QR-Code (encryption).
* Then, the program asks for the voter to read with the code-reader the second QR-Code (randomness).
* The program executes the algorithm and shows the candidate that is encrypted in the ballot.
* After this, the program "resets" and asks again for a new pair of QR-Codes of the next voter.