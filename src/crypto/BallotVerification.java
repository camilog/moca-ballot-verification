package crypto;

import com.google.gson.Gson;

import com.googlecode.lanterna.gui2.MultiWindowTextGUI;

import objects.AuthorityPublicKey;
import objects.Candidate;
import objects.Election;
import objects.PlainVote;

import paillierp.Paillier;
import paillierp.key.PaillierKey;

import org.xml.sax.SAXException;
import javax.xml.parsers.ParserConfigurationException;
import java.io.*;
import java.math.BigInteger;
import java.util.Random;

public class BallotVerification {

    private static BigInteger encryptedCandidate = null;
    private static BigInteger randomness = null;
    private static String[] candidates = null;
    private static Paillier paillierPublic = null;

    // Configuration of the public information stored locally
    public static void publicConfiguration(String electionInfo, String publicKeyInfo) throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException {

        AuthorityPublicKey authPublicKey = new Gson().fromJson(publicKeyInfo, AuthorityPublicKey.class);
        String publicKeyString = authPublicKey.getN();

        // Recover publicKey from local file
        BigInteger publicKeyN = new BigInteger(publicKeyString);

        // Create Paillier scheme with given publicKey
        PaillierKey publicKey = new PaillierKey(publicKeyN, new Random());
        paillierPublic = new Paillier(publicKey);

        // Set-up the list of candidates
        candidates = setCandidates(electionInfo);

    }

    // Set the values of the read ballot
    //@ requires encryptedBallotWithSignature != null && randomnessString != null;
    //@ ensures encryptedCandidate > 0 && randomness > 0
    public static void ballotConfiguration(String encryptedBallotWithSignature, String randomnessString) {

        // Separate text from ballot in: encryptedVote and signature
        String[] encryptionAndSignature = separateBallot(encryptedBallotWithSignature);
        String encryptedVoteString = encryptionAndSignature[0];

        // Create BigInteger of the encryption
        encryptedCandidate = new BigInteger(encryptedVoteString);

        // Create BigInteger randomness
        randomness = new BigInteger(randomnessString);

    }

    // Separate the read ballot into encrypted vote and signature
    private static String[] separateBallot(String encryptedBallotWithSignature) {
        return encryptedBallotWithSignature.split("#");
    }

    // Algorithm of verification of the encryption printed on the ballot
    //@ requires encryptedCandidate != null && randomness != null && candidates != null && paillierPublic != null;
    //@ ensures \result != null
    public static String verification() {

        // Variable to store the candidate encrypted. By default there's no valid encrypted candidate
        String finalCandidate = "THERE'S NO VALID CANDIDATE ENCRYPTED";

        // Set the real number of candidates. The array candidates has additionally the 'blank vote'
        int numberOfCandidates = candidates.length - 1;

        // Create the first possible candidate encrypted
        PlainVote plainVote = new PlainVote(numberOfCandidates, 1);

        // Encrypt the possible candidate with the same randomness.
        // If it's the same as the encrypted one, set finalCandidate and break,
        // if not, try a different candidate
        for (int i = 0; i < candidates.length; ++i) {
            BigInteger voteBI = plainVote.toBigInteger();
            BigInteger possibleEncryption = paillierPublic.encrypt(voteBI, randomness);
            if (possibleEncryption.equals(encryptedCandidate)) {
                finalCandidate = candidates[i];
                break;
            }
            else
                plainVote = new PlainVote(numberOfCandidates, i+2);
        }

        return finalCandidate;

    }

    // Retrieve the list of candidates
    public static String[] getCandidates() {
        return candidates;
    }

    // Retrieve the Paillier scheme made with the public key retrieved
    public static Paillier getPaillierPublic() {
        return paillierPublic;
    }

    // Function to set-up the candidates from a local file called candidatesList.json (which must be configured at the start of the application)
    private static String[] setCandidates(String electionInfo) throws IOException {
        Gson gson = new Gson();
        Election election = gson.fromJson(electionInfo, Election.class);
        String[] candidates = new String[election.getNumber_of_candidates() + 1];

        int i = 0;
        for (Candidate candidate : election.getCandidates()) {
            candidates[i] = candidate.getName();
            i++;
        }

        // FIX THIS!
        candidates[i] = "Voto Blanco";

        return candidates;

    }

}
