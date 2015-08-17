import com.googlecode.lanterna.gui.GUIScreen;
import com.googlecode.lanterna.gui.dialog.FileDialog;
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

    private static BigInteger encryptedCandidate = null;
    private static BigInteger randomness = null;
    private static String[] candidates = null;
    private static Paillier paillierPublic = null;
    private static GUIScreen guiScreen;

    protected static void setGuiScreen(GUIScreen screen) {
        guiScreen = screen;
    }

    protected static void publicConfiguration() throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException {

        // Recover publicKey from local file
        BigInteger publicKeyN = recoverPublicKey();

        // Create Paillier scheme with given publicKey
        PaillierKey publicKey = new PaillierKey(publicKeyN, new Random());
        paillierPublic = new Paillier(publicKey);

        // Set-up the list of candidates
        candidates = setCandidates();

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

        String finalCandidate = "THERE'S NO VALID CANDIDATE ENCRYPTED";

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
    //@ ensures \result > 0
    private static BigInteger recoverPublicKey() throws IOException, ClassNotFoundException {
        String fileName;
        fileName = FileDialog.showOpenFileDialog(guiScreen, new File("/home/"), "Choose Public Key file").getPath();
        ObjectInputStream oin = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)));
        return (BigInteger) oin.readObject();
    }

    public static String[] getCandidates() {
        return candidates;
    }

    public static Paillier getPaillierPublic() {
        return paillierPublic;
    }

    // Function to set-up the candidates from a local file called candidates.xml (which is stored in candidates folder)
    // Because of how is written candidates.xml, it needs this function to store in a String[] the different candidates
    //@ requires folderName != null
    private static String[] setCandidates() throws ParserConfigurationException, IOException, SAXException {
        String candidatesFile;
        candidatesFile = FileDialog.showOpenFileDialog(guiScreen, new File("/home"), "Choose candidates.xml file").getPath();
        File file = new File(candidatesFile);

        String[] candidates;

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

}
