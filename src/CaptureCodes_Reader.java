import com.google.gson.Gson;
import com.googlecode.lanterna.TerminalFacade;
import com.googlecode.lanterna.gui.GUIScreen;
import com.googlecode.lanterna.gui.Window;
import com.googlecode.lanterna.gui.component.Button;
import com.googlecode.lanterna.gui.dialog.MessageBox;
import com.googlecode.lanterna.screen.Screen;

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
import java.net.HttpURLConnection;
import java.net.URL;
import java.util.Random;

public class CaptureCodes_Reader extends Window {

    private static final String authorityPublicKeyServer = "http://cjgomez.duckdns.org:3000/authority_public_keys";
    // private static final String candidatesServer = "http://cjgomez.duckdns.org:3000/candidates";

    public CaptureCodes_Reader() {
        super("Ballot Encryption Verification");

        // Add button to configurate the publicInformation
        addComponent(new Button("Configurate Public Information", () -> {
            try {
                downloadAuthPublicKey(authorityPublicKeyServer);
                // downloadCandidatesFile(candidatesServer);
            } catch (IOException e) {
                e.printStackTrace();
            }

        }));

        // Add button to initialize application
        addComponent(new Button("Initialize verification", () -> {
            // TODO: apretar OK automaticamente en la nueva ventana
            // Retrieve first QR-Code (encryptedBallot + signature)
            String encryptedBallotWithSignature = com.googlecode.lanterna.gui.dialog.TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read FIRST QR-Code", "", 1000);

            // Retrieve second QR-Code (randomness used to encrypt)
            String randomnessString = com.googlecode.lanterna.gui.dialog.TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read SECOND QR-Code", "", 1000);

            // Initialize encryptedCandidate to show later
            String encryptedCandidate = "";

            // Apply algorithm to try all possible candidates and stores in encryptedCandidate the one who is actually encrypted
            try {
                encryptedCandidate = procedure(encryptedBallotWithSignature, randomnessString);
            } catch (IOException | SAXException | ParserConfigurationException | ClassNotFoundException e) {
                e.printStackTrace();
            }

            // Final message which shows the encryptedCandidate, if none, shows an empty String
            MessageBox.showMessageBox(getOwner(), "Candidato Encriptado", encryptedCandidate);
        }));

        // Add button to finalize application
        addComponent(new Button("Exit application", () -> {
            // Close window properly and finalize application
            getOwner().getScreen().clear();
            getOwner().getScreen().refresh();
            getOwner().getScreen().setCursorPosition(0, 0);
            getOwner().getScreen().refresh();
            getOwner().getScreen().stopScreen();
            System.exit(0);
        }));

    }

    // Download and store Public Key of the Authority from the BB
    private void downloadAuthPublicKey(String authorityPublicKeyServer) throws IOException {
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

    }

    /*
    // Download and store Candidates file from the BB
    private void downloadCandidatesFile(String authorityPublicKeyServer) {
        File candidatesFile = new File("candidates/candidates.xml");

        // TODO: Analizar si archivo se suberá en un servidor FTP o en la Base de datos.

    }
    */

    static public void main(String[] args) throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException, InterruptedException {

        // Create window to display options
        CaptureCodes_Reader myWindow = new CaptureCodes_Reader();
        GUIScreen guiScreen = TerminalFacade.createGUIScreen();
        Screen screen = guiScreen.getScreen();

        // TODO: refrescar la pantalla al terminar cada operación

        // Start and configuration of the screen
        screen.startScreen();
        guiScreen.showWindow(myWindow, GUIScreen.Position.CENTER);
        screen.refresh();

        // Stopping screen at finalize application
        screen.stopScreen();

    }

    private static String procedure(String encryptedBallotWithSignature, String randomnessString) throws IOException, SAXException, ParserConfigurationException, ClassNotFoundException {
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

    }

    // Function to retrieve publicKey (BigInteger object) from local file
    private static BigInteger recoverPublicKey(String fileName) throws IOException, ClassNotFoundException {
        ObjectInputStream oin = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)));
        return (BigInteger) oin.readObject();
    }

    // Function to set-up the candidates from a local file called candidates.xml (which is stored in candidates folder)
    private static String[] setCandidates(String folderName) throws ParserConfigurationException, IOException, SAXException {
        // Because of how is written candidates.xml, it needs this function to store in a String[] the different candidates
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

}
