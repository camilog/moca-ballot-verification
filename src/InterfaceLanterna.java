import com.googlecode.lanterna.TerminalFacade;
import com.googlecode.lanterna.gui.GUIScreen;
import com.googlecode.lanterna.gui.Window;
import com.googlecode.lanterna.gui.component.Button;
import com.googlecode.lanterna.gui.dialog.MessageBox;
import com.googlecode.lanterna.screen.Screen;

import org.xml.sax.SAXException;

import javax.xml.parsers.ParserConfigurationException;
import java.io.*;

public class InterfaceLanterna extends Window {

    public InterfaceLanterna() {
        super("Ballot Encryption Verification");

        // Add button to configurate the publicInformation
        addComponent(new Button("Configurate Public Information", () -> {
            try {
                BallotVerification.publicConfiguration();
                // downloadCandidatesFile(candidatesServer);
            } catch (IOException | ClassNotFoundException | SAXException | ParserConfigurationException e) {
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

            // Apply algorithm to try all possible candidates and stores in encryptedCandidate the one who is actually encrypted
            BallotVerification.ballotConfiguration(encryptedBallotWithSignature, randomnessString);
            String finalCandidate = BallotVerification.verification();

            // Final message which shows the encryptedCandidate, if none, shows an empty String
            MessageBox.showMessageBox(getOwner(), "Candidato Encriptado", finalCandidate);
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

    static public void main(String[] args) throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException, InterruptedException {

        // Create window to display options
        InterfaceLanterna myWindow = new InterfaceLanterna();
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

}
