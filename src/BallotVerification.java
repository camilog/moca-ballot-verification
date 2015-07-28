import org.w3c.dom.Document;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;
import org.xml.sax.SAXException;
import paillierp.Paillier;
import paillierp.key.PaillierKey;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.*;
import java.math.BigInteger;
import java.util.Random;

public class BallotVerification {

    // private static final String authorityPublicKeyServer = "http://cjgomez.duckdns.org:3000/authority_public_keys";
    // private static final String candidatesServer = "http://cjgomez.duckdns.org:3000/candidates";

    private static BigInteger encryptedCandidate = null;
    private static BigInteger randomness = null;
    private static String[] candidates = null;
    private static Paillier paillierPublic = null;

    protected static void publicConfiguration() throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException {

        // Recover publicKey from local file
        BigInteger publicKeyN = recoverPublicKey("publicValueForEncryption/publicKeyN.key");

        // Create Paillier scheme with given publicKey
        PaillierKey publicKey = new PaillierKey(publicKeyN, new Random());
        paillierPublic = new Paillier(publicKey);

        // Set-up the list of candidates
        candidates = setCandidates("candidates/");

    }

    //@ requires encryptedBallotWithSignature != null && randomnessString != null;
    //@ ensures encryptedCandidate > 0 && randomness > 0
    protected static void ballotConfiguration(String encryptedBallotWithSignature, String randomnessString) {

        // Separate text from ballot in: length of ballot(sep) + ballot + signature, and create BigInteger ballot
        int sep = Integer.parseInt(encryptedBallotWithSignature.substring(0, 3));
        String encryptedBallotString = encryptedBallotWithSignature.substring(3, sep + 3);
        encryptedCandidate = new BigInteger(encryptedBallotString);

        // Create BigInteger randomness
        randomness = new BigInteger(randomnessString);

    }

    // Algorithm of verification of the encryption printed on the ballot
    //@ requires encryptedCandidate != null && randomness != null && candidates != null && paillierPublic != null;
    //@ ensures \result != null
    protected static String verification() {

        String finalCandidate = "NO EXISTE UN CANDIDATO VÁLIDO ENCRIPTADO";

        byte[] possibleBallot = new byte[candidates.length + 1];
        possibleBallot[0] = 1;

        // Inicio = possibleBallot[0] = 1 y sum(possibleBallot) = 1
        // Durante = possibleBallot[0] = 1 y sum(possibleBallot) = 2
        // Final
        for (int i = 0; i < possibleBallot.length - 1; i++) {
            possibleBallot[i+1] = 1;
            BigInteger possibleEncryption = paillierPublic.encrypt(new BigInteger(possibleBallot), randomness);
            if (possibleEncryption.equals(encryptedCandidate)) {
                finalCandidate = candidates[i];
                break;
            }
            else
                possibleBallot[i+1] = 0;
        }

        return finalCandidate;

    }

    // Function to retrieve publicKey (BigInteger object) from local file
    //@ requires fileName != null
    //@ ensures \result > 0
    private static BigInteger recoverPublicKey(String fileName) throws IOException, ClassNotFoundException {
        ObjectInputStream oin = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)));
        return (BigInteger) oin.readObject();
    }

    // Function to set-up the candidates from a local file called candidates.xml (which is stored in candidates folder)
    // Because of how is written candidates.xml, it needs this function to store in a String[] the different candidates
    //@ requires folderName != null
    private static String[] setCandidates(String folderName) throws ParserConfigurationException, IOException, SAXException {
        String[] candidates;
        File file = new File(folderName + "candidates.xml");
        DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
        DocumentBuilder db = dbf.newDocumentBuilder();
        Document doc = db.parse(file);
        doc.getDocumentElement().normalize();

        NodeList nodeLst = doc.getElementsByTagName("integer");
        int numberOfCandidates = Integer.parseInt(nodeLst.item(0).getTextContent());
        candidates = new String[numberOfCandidates + 1];
        nodeLst = doc.getElementsByTagName("string");

        for (int i = 0 ; i < nodeLst.getLength() ; i++) {
            Node node = nodeLst.item(i);
            candidates[i] = node.getTextContent();
        }

        return candidates;
    }

    // Download and store Public Key of the Authority from the BB
    /*static protected void downloadAuthPublicKey(String authorityPublicKeyServer) throws IOException {
        // Create file where to store the publicKey of the authority
        File authPublicKeyFile = new File("publicValueForEncryption" + File.separator + "publicKeyN.key");

        // Set the URL to GET the public key of the authority
        URL obj = new URL(authorityPublicKeyServer);
        HttpURLConnection con = (HttpURLConnection) obj.openConnection();

        // Add request header
        con.setRequestMethod("GET");
        con.setRequestProperty("Content-Type", "application/json");
        con.getResponseCode();

        // Receive the response
        BufferedReader in = new BufferedReader(new InputStreamReader(con.getInputStream()));
        String inputLine;
        StringBuilder response = new StringBuilder();
        while ((inputLine = in.readLine()) != null) {
            response.append(inputLine);
        }
        in.close();

        // Process JSON as an object to extract the key
        String jsonString = response.toString();
        Gson gson = new Gson();
        AuthorityPublicKey[] voterPublicKey = gson.fromJson(jsonString, AuthorityPublicKey[].class);
        String authPublicKey_key = voterPublicKey[0].key;

        // Write the public key in the File
        BufferedWriter writer = new BufferedWriter(new FileWriter(authPublicKeyFile));
        writer.write(authPublicKey_key);
        writer.close();

    }*/

    /*protected static String procedure(String encryptedBallotWithSignature, String randomnessString) throws IOException, SAXException, ParserConfigurationException, ClassNotFoundException {
        // Separate text from ballot in: length of ballot(sep) + ballot + signature, and create BigInteger ballot
        int sep = Integer.parseInt(encryptedBallotWithSignature.substring(0, 3));
        String encryptedBallotString = encryptedBallotWithSignature.substring(3, sep + 3);
        BigInteger ballot = new BigInteger(encryptedBallotString);

        // Create BigInteger randomness
        BigInteger randomness = new BigInteger(randomnessString);

        // Recover publicKey from local file
        BigInteger publicKeyN = recoverPublicKey("publicValueForEncryption/publicKeyN.key");

        // Create Paillier scheme with given publicKey
        PaillierKey publicKey = new PaillierKey(publicKeyN, new Random());
        Paillier p = new Paillier(publicKey);

        // Set-up the list of candidates and variable to save the possible encrypted candidate
        String[] candidates = setCandidates("candidates/");
        byte[] possibleBallot = new byte[candidates.length + 1];
        possibleBallot[0] = 1;
        String encryptedCandidate = "No hay candidato encriptado";

        // Apply algorith to try all posible candidates and give the encrypted candidate in the ballot
        for (int i = 0; i < possibleBallot.length - 1; i++){
            possibleBallot[i+1] = 1;
            BigInteger enc = p.encrypt(new BigInteger(possibleBallot), randomness);
            if (enc.equals(ballot)) {
                encryptedCandidate = candidates[i];
                break;
            }
            else
                possibleBallot[i+1] = 0;
        }

        // Return encryptedCandidate in the ballot. If none, returns "No hay candidato encriptado"
        return encryptedCandidate;

    }*/

}
