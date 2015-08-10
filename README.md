# BallotVerification
Fourth part of the [*MoCa QR*](https://github.com/CamiloG/moca_qr) Voting System project.

Verifies that the selection made in [BallotSelection](https://github.com/CamiloG/BallotSelection) was encrypted in the printed ballot.

## Files
1. **GUILanterna.java**:
2. **AuthorityPublicKey.java**:

## How to Use
* Download the .jar file [here](https://github.com/CamiloG/moca_qr/blob/master/Precinct_Apps/BallotVerification.jar?raw=true).
* Put the file ballotVerification.jar in the project folder.

### Configuration
* Execute ballotVerification.jar with `$ java -jar ballotVerification.jar`
* Select "Configure Public Information" (just the first time) to download the necessary values from the Bulletin Board server: candidates/candidates.xml and publicValueForEncryption/publicKeyN.key.

### Verification Process
* After configuration, select "Initialize Verification".
* Next, the program asks for the voter to read with the code-reader the first QR-Code (encryption).
* Then, the program asks for the voter to read with the code-reader the second QR-Code (randomness).
* The program executes the algorithm and shows the candidate that is encrypted in the ballot.
* After this, the program "resets" and asks again for a new pair of QR-Codes of the next voter.