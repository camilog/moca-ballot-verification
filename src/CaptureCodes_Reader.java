import com.googlecode.lanterna.TerminalFacade;
import com.googlecode.lanterna.gui.GUIScreen;
import com.googlecode.lanterna.gui.Theme;
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
import java.security.NoSuchAlgorithmException;
import java.util.Random;

public class CaptureCodes_Reader extends Window {

    public CaptureCodes_Reader() {
        super("Ballot Encryption Verification");

        addComponent(new Button("Initialize verification", () -> {
            // TODO: apretar OK automaticamente en la nueva ventana
            String ballotWithSignature = com.googlecode.lanterna.gui.dialog.TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read FIRST QR-Code", "", 1000);
            String randomnessString = com.googlecode.lanterna.gui.dialog.TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read SECOND QR-Code", "", 1000);

            String encryptedCandidate = "";

            try {
                encryptedCandidate = procedure(ballotWithSignature, randomnessString);
            } catch (IOException e) {
                e.printStackTrace();
            } catch (SAXException e) {
                e.printStackTrace();
            } catch (ParserConfigurationException e) {
                e.printStackTrace();
            } catch (ClassNotFoundException e) {
                e.printStackTrace();
            }

            MessageBox.showMessageBox(getOwner(), "Candidato Encriptado", encryptedCandidate);
        }));

        addComponent(new Button("Exit application", () -> {
            // Salirse del window
            getOwner().getScreen().clear();
            getOwner().getScreen().refresh();
            getOwner().getScreen().setCursorPosition(0, 0);
            getOwner().getScreen().refresh();
            getOwner().getScreen().stopScreen();
            System.exit(0);
        }));


    }

    static public void main(String[] args) throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException, InterruptedException {

        CaptureCodes_Reader myWindow = new CaptureCodes_Reader();
        GUIScreen guiScreen = TerminalFacade.createGUIScreen();
        Screen screen = guiScreen.getScreen();

        // TODO: refrescar la pantalla al terminar la operación

        screen.startScreen();
        guiScreen.showWindow(myWindow, GUIScreen.Position.CENTER);
        screen.refresh();
        screen.stopScreen();

    }

    private static String procedure(String ballotWithSignature, String randomnessString) throws IOException, SAXException, ParserConfigurationException, ClassNotFoundException {
        BigInteger publicKeyN = recoverPublicKey("publicValueForEncryption/publicKeyN.key");

        PaillierKey publicKey = new PaillierKey(publicKeyN, new Random());
        Paillier p = new Paillier(publicKey);

        int sep = Integer.parseInt(ballotWithSignature.substring(0, 3));
        BigInteger ballot = new BigInteger(ballotWithSignature.substring(3, sep+3));

        BigInteger randomness = new BigInteger(randomnessString);

        String[] candidates = setCandidates("candidates/");
        byte[] possibleBallot = new byte[candidates.length + 1];
        possibleBallot[0] = 1;
        String encryptedCandidate = "No hay candidato encriptado";

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

        return encryptedCandidate;

    }

    private static BigInteger recoverPublicKey(String fileName) throws IOException, ClassNotFoundException {
        ObjectInputStream oin = new ObjectInputStream(new BufferedInputStream(new FileInputStream(fileName)));
        BigInteger publicKeyN = (BigInteger) oin.readObject();
        return publicKeyN;
    }

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

}
