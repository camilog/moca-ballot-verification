import com.googlecode.lanterna.TerminalFacade;
import com.googlecode.lanterna.gui.GUIScreen;
import com.googlecode.lanterna.gui.Window;
import com.googlecode.lanterna.gui.component.Button;
import com.googlecode.lanterna.gui.component.Label;
import com.googlecode.lanterna.gui.component.Panel;
import com.googlecode.lanterna.gui.dialog.DialogButtons;
import com.googlecode.lanterna.gui.dialog.MessageBox;
import com.googlecode.lanterna.gui.dialog.TextInputDialog;
import com.googlecode.lanterna.screen.Screen;

import org.xml.sax.SAXException;

import javax.xml.parsers.ParserConfigurationException;
import java.io.*;

public class GUILanterna extends Window {

    public GUILanterna() {
        super("Ballot Encryption Verification");

        // Panel with the public information (already configure or not)
        Panel publicInformationPanel = new Panel("Configuration of Public Information");
        publicInformationPanel.addComponent(new Label("Public Key: NO"));
        publicInformationPanel.addComponent(new Label("Candidates File: NO"));

        // Add public information panel
        addComponent(publicInformationPanel);
        updatePublicInformationLabel(publicInformationPanel);

        // Add button to configurate the publicInformation
        addComponent(new Button("Configurate Public Information", () -> {

            String candidates = TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read Candidates QR-Code","",1000);
            String publicKey = TextInputDialog.showTextInputBox(getOwner(),"Codes Reader", "Read Public Key QR-Code","",1000);
            try {
                BallotVerification.publicConfiguration(candidates, publicKey);
                updatePublicInformationLabel(publicInformationPanel);
            } catch (IOException | ClassNotFoundException | SAXException | ParserConfigurationException e) {
                e.printStackTrace();
            }

        }));

        // Add button to initialize application
        addComponent(new Button("Initialize verification", () -> {
            // TODO: apretar OK automaticamente en las nuevas ventanas, luego de introducir código QR

            // Retrieve first QR-Code (encryptedBallot + signature)
            String encryptedBallotWithSignature = TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read FIRST QR-Code", "", 1000);
            // TODO: Check if the user pressed 'Cancel' -> La idea es que no sea posible, debido a apretar automáticamente 'OK'

            // Retrieve second QR-Code (randomness used to encrypt)
            String randomnessString = TextInputDialog.showTextInputBox(getOwner(), "Codes Reader", "Read SECOND QR-Code", "", 1000);
            // TODO: Check if the user pressed 'Cancel' -> La idea es que no sea posible, debido a apretar automáticamente 'OK'

            // Apply algorithm to try all possible candidates and stores in encryptedCandidate the one who is actually encrypted
            BallotVerification.ballotConfiguration(encryptedBallotWithSignature, randomnessString);
            String finalCandidate = BallotVerification.verification();

            // Final message which shows the encryptedCandidate, if none, shows an empty String
            MessageBox.showMessageBox(getOwner(), "Encrypted Candidate", finalCandidate, DialogButtons.OK);
            // TODO: Reiniciar aplicación luego de pasado un cierto tiempo

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

    private void updatePublicInformationLabel(Panel publicInformationPanel) {

        Label publicKeyLabel = (Label) publicInformationPanel.getComponentAt(0);
        Label candidatesFileLabel = (Label) publicInformationPanel.getComponentAt(1);

        if (BallotVerification.getPaillierPublic() != null)
            publicKeyLabel.setText("Public Key: YES");

        if (BallotVerification.getCandidates() != null)
            candidatesFileLabel.setText("Candidates File: YES");

    }

    static public void main(String[] args) throws IOException, ClassNotFoundException, ParserConfigurationException, SAXException, InterruptedException {

        // Create window to display options
        GUILanterna myWindow = new GUILanterna();
        GUIScreen guiScreen = TerminalFacade.createGUIScreen();
        BallotVerification.setGuiScreen(guiScreen);
        Screen screen = guiScreen.getScreen();

        // Start and configuration of the screen
        screen.startScreen();
        guiScreen.showWindow(myWindow, GUIScreen.Position.CENTER);
        screen.refresh();

        // Stopping screen at finalize application
        screen.stopScreen();

    }

}
