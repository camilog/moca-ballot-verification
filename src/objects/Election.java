package objects;

public class Election {

    private Candidate[] candidates;
    private int number_of_candidates;
    private String question;

    public Candidate[] getCandidates() {
        return candidates;
    }

    public int getNumber_of_candidates() {
        return number_of_candidates;
    }

    public String getQuestion() {
        return question;
    }
}
