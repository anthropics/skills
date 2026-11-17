#include <pybind11/pybind11.h>
#include <pybind11/stl.h>
#include <pybind11/numpy.h>
#include <vector>
#include <random>
#include <cmath>
#include <algorithm>
#include <iostream>

namespace py = pybind11;

// -------------------------------------------------
// Utility functions
// -------------------------------------------------
double randn(std::mt19937 &gen) {
    static std::normal_distribution<> dist(0.0, 1.0);
    return dist(gen);
}

std::vector<double> tanh_vec(const std::vector<double>& x) {
    std::vector<double> out(x.size());
    for (size_t i = 0; i < x.size(); i++)
        out[i] = std::tanh(x[i]);
    return out;
}

std::vector<double> tanh_derivative(const std::vector<double>& x) {
    std::vector<double> out(x.size());
    for (size_t i = 0; i < x.size(); i++) {
        double t = std::tanh(x[i]);
        out[i] = 1.0 - t * t;
    }
    return out;
}

std::vector<double> vec_sub(const std::vector<double>& a, const std::vector<double>& b) {
    std::vector<double> out(a.size());
    for (size_t i = 0; i < a.size(); i++)
        out[i] = a[i] - b[i];
    return out;
}

std::vector<double> vec_mul(const std::vector<double>& a, const std::vector<double>& b) {
    std::vector<double> out(a.size());
    for (size_t i = 0; i < a.size(); i++)
        out[i] = a[i] * b[i];
    return out;
}

std::vector<double> vec_scalar_mul(const std::vector<double>& a, double s) {
    std::vector<double> out(a.size());
    for (size_t i = 0; i < a.size(); i++)
        out[i] = a[i] * s;
    return out;
}

std::vector<double> matvec(
    const std::vector<std::vector<double>>& W,
    const std::vector<double>& x
) {
    std::vector<double> out(W.size(), 0.0);
    for (size_t i = 0; i < W.size(); i++)
        for (size_t j = 0; j < x.size(); j++)
            out[i] += W[i][j] * x[j];
    return out;
}

std::vector<double> matvecT(
    const std::vector<std::vector<double>>& W,
    const std::vector<double>& x
) {
    std::vector<double> out(W[0].size(), 0.0);
    for (size_t i = 0; i < W.size(); i++)
        for (size_t j = 0; j < W[i].size(); j++)
            out[j] += W[i][j] * x[i];
    return out;
}

// -------------------------------------------------
// Model
// -------------------------------------------------
class MultiLayerPredictiveCodingNetwork {
public:
    std::vector<int> layer_sizes;
    double learningRate;
    double paramLearningRate;

    std::vector<double> layer_log_variances;
    std::vector<double> input_log_variance;

    std::vector<std::vector<std::vector<double>>> weights;

    std::vector<double> allPredictions;
    std::vector<double> allTargets;

    std::mt19937 weight_gen;
    std::mt19937 inference_gen;
    std::mt19937 shuffle_gen;

    // Constructor
    MultiLayerPredictiveCodingNetwork(
        std::vector<int> layer_sizes,
        double learningRate = 0.01,
        py::object variances = py::none(),
        py::object paramLearningRate = py::none(),
        py::object seed = py::none()
    ) {

        int base_seed;

        if (!seed.is_none())
            base_seed = seed.cast<int>();
        else
            base_seed = std::random_device{}();

        weight_gen.seed(base_seed);
        inference_gen.seed(base_seed + 1);
        shuffle_gen.seed(base_seed + 2);

        this->layer_sizes = layer_sizes;
        this->learningRate = learningRate;
        this->paramLearningRate = paramLearningRate.is_none()
            ? learningRate
            : paramLearningRate.cast<double>();

        if (variances.is_none()) {
            layer_log_variances.resize(layer_sizes.size(), std::log(1.0));
        } else {
            auto v = variances.cast<std::vector<double>>();
            for (auto val : v)
                layer_log_variances.push_back(std::log(val));
        }

        input_log_variance.resize(layer_sizes[0], 0.0);

        // Xavier init
        for (size_t i = 0; i < layer_sizes.size() - 1; i++) {
            int fan_in = layer_sizes[i + 1];
            int fan_out = layer_sizes[i];
            double std = std::sqrt(2.0 / (fan_in + fan_out));

            std::vector<std::vector<double>> W(fan_out, std::vector<double>(fan_in));

            for (int r = 0; r < fan_out; r++)
                for (int c = 0; c < fan_in; c++)
                    W[r][c] = randn(weight_gen) * std;

            weights.push_back(W);
        }
    }

    // Inference
    std::pair<
        std::vector<std::vector<double>>,
        std::vector<std::vector<double>>
    >
    infer(
        std::vector<double> observed_input,
        py::object supervised_target,
        int max_iterations,
        double tol = 5e-3
    ) {

        std::vector<std::vector<double>> states;

        for (int size : layer_sizes) {
            std::vector<double> s(size);
            for (double &v : s) v = randn(inference_gen) * 0.01;
            states.push_back(s);
        }

        states[0] = observed_input;

        auto prev_states = states;

        std::vector<double> input_precision(input_log_variance.size());
        for (size_t i = 0; i < input_precision.size(); i++)
            input_precision[i] = std::exp(-input_log_variance[i]);

        std::vector<double> layer_precision(layer_log_variances.size());
        for (size_t i = 0; i < layer_precision.size(); i++)
            layer_precision[i] = std::exp(-layer_log_variances[i]);

        std::vector<std::vector<double>> errors(states.size());

        for (int it = 0; it < max_iterations; it++) {

            std::vector<std::vector<double>> acts;
            std::vector<std::vector<double>> slopes;

            for (auto &s : states) {
                auto a = tanh_vec(s);
                acts.push_back(a);

                std::vector<double> d(a.size());
                for (size_t i = 0; i < a.size(); i++)
                    d[i] = 1.0 - a[i] * a[i];
                slopes.push_back(d);
            }

            std::vector<std::vector<double>> preds;
            for (size_t i = 0; i < weights.size(); i++)
                preds.push_back(matvec(weights[i], acts[i + 1]));

            // INPUT ERROR
            auto residual0 = vec_sub(states[0], preds[0]);
            errors[0] = vec_mul(input_precision, residual0);

            // HIDDEN ERRORS
            for (size_t i = 1; i < states.size() - 1; i++) {
                auto r = vec_sub(states[i], preds[i]);
                errors[i] = vec_scalar_mul(r, layer_precision[i]);
            }

            // OUTPUT ERROR
            std::vector<double> output_error(states.back().size());

            if (!supervised_target.is_none()) {
                auto target = supervised_target.cast<std::vector<double>>();
                auto a = acts.back();

                for (size_t i = 0; i < a.size(); i++)
                    output_error[i] = layer_precision.back() * (target[i] - a[i]);
            } else {
                auto a = acts.back();
                for (size_t i = 0; i < a.size(); i++)
                    output_error[i] = layer_precision.back() * (-a[i]);
            }

            errors.back() = output_error;

            // STATE UPDATES
            for (size_t i = 1; i < states.size() - 1; i++) {

                auto bottom = matvecT(weights[i - 1], errors[i - 1]);
                bottom = vec_mul(bottom, slopes[i]);

                auto top = vec_scalar_mul(errors[i], -1.0);

                for (size_t j = 0; j < states[i].size(); j++)
                    states[i][j] += learningRate * (bottom[j] + top[j]);
            }

            for (size_t j = 0; j < states.back().size(); j++)
                states.back()[j] += (learningRate * errors.back()[j] * slopes.back()[j]);

            double max_change = 0.0;

            for (size_t i = 1; i < states.size(); i++)
                for (size_t j = 0; j < states[i].size(); j++)
                    max_change = std::max(
                        max_change,
                        std::abs(states[i][j] - prev_states[i][j])
                    );

            if (max_change < tol)
                break;

            prev_states = states;
        }

        return {states, errors};
    }

    // -------------------------------------------------
// Activation helper
// -------------------------------------------------
    std::vector<double> activation(
        const std::vector<double>& x
    ) {
        return tanh_vec(x);
    }

    // -------------------------------------------------
    // Parameter updates
    // -------------------------------------------------
    void updateParameters(
        const std::vector<std::vector<double>>& states,
        const std::vector<std::vector<double>>& errors
    ) {

        auto activities = states;

        for (auto& a : activities)
            a = tanh_vec(a);

        // Weight updates
        for (size_t layer = 0; layer < weights.size(); layer++) {

            for (size_t row = 0; row < weights[layer].size(); row++) {

                for (size_t col = 0; col < weights[layer][row].size(); col++) {

                    double gradient =
                        errors[layer][row] *
                        activities[layer + 1][col];

                    weights[layer][row][col] +=
                        paramLearningRate * gradient;

                    weights[layer][row][col] =
                        std::clamp(
                            weights[layer][row][col],
                            -10.0,
                            10.0
                        );
                }
            }
        }

        // Input variance learning
        for (size_t i = 0; i < input_log_variance.size(); i++) {

            input_log_variance[i] +=
                paramLearningRate *
                (
                    errors[0][i] * errors[0][i]
                    - 1.0
                    );

            input_log_variance[i] =
                std::clamp(
                    input_log_variance[i],
                    -5.0,
                    5.0
                );
        }

        // Hidden/output variance learning
        for (size_t layer = 1; layer < errors.size(); layer++) {

            double mean_error = 0.0;

            for (double e : errors[layer])
                mean_error += e * e;

            mean_error /= errors[layer].size();

            layer_log_variances[layer] +=
                paramLearningRate *
                (mean_error - 1.0);

            layer_log_variances[layer] =
                std::clamp(
                    layer_log_variances[layer],
                    -5.0,
                    5.0
                );
        }
    }

    // -------------------------------------------------
    // R² metric
    // -------------------------------------------------
    double computeRSquared() {

        if (allTargets.size() < 2)
            return 0.0;

        double mean_target = 0.0;

        for (double t : allTargets)
            mean_target += t;

        mean_target /= allTargets.size();

        double total_variance = 0.0;
        double residual_variance = 0.0;

        for (size_t i = 0; i < allTargets.size(); i++) {

            total_variance +=
                std::pow(allTargets[i] - mean_target, 2);

            residual_variance +=
                std::pow(allTargets[i] - allPredictions[i], 2);
        }

        if (total_variance == 0.0)
            return 0.0;

        return 1.0 - (residual_variance / total_variance);
    }

    // -------------------------------------------------
    // Training
    // -------------------------------------------------
    void train(
        std::vector<
        std::pair<
        std::vector<double>,
        std::vector<double>
        >
        > dataset,
        int epochs = 40,
        int steps = 30,
        bool shuffle = true
    ) {

        std::vector<double> variance_history;

        for (int epoch = 0; epoch < epochs; epoch++) {

            allPredictions.clear();
            allTargets.clear();

            if (shuffle) {
                std::shuffle(
                    dataset.begin(),
                    dataset.end(),
                    shuffle_gen
                );
            }

            for (auto& sample : dataset) {

                auto inputData = sample.first;
                auto targetOutput = sample.second;

                auto inference_result =
                    infer(
                        inputData,
                        py::cast(targetOutput),
                        steps
                    );

                auto states = inference_result.first;
                auto errors = inference_result.second;

                double prediction =
                    std::tanh(states.back()[0]);

                allPredictions.push_back(prediction);
                allTargets.push_back(targetOutput[0]);

                updateParameters(states, errors);
            }

            variance_history.push_back(
                computeRSquared()
            );
        }

        double avg = 0.0;

        for (double v : variance_history)
            avg += v;

        avg /= variance_history.size();

        std::cout
            << "After "
            << epochs
            << " epochs and "
            << steps 
            << " steps the average variance is "
            << avg
            << std::endl;
    }

    // -------------------------------------------------
    // Prediction
    // -------------------------------------------------
    std::vector<double> predict(
        std::vector<double> inputData,
        int steps = 50
    ) {

        auto result =
            infer(
                inputData,
                py::none(),
                steps
            );

        auto states = result.first;

        return tanh_vec(states.back());
    }

    // -------------------------------------------------
    // Feature importance
    // -------------------------------------------------
    std::vector<double> getInputVariances() {

        std::vector<double> variances(
            input_log_variance.size()
        );

        for (size_t i = 0; i < variances.size(); i++)
            variances[i] =
            std::exp(input_log_variance[i]);

        return variances;
    }

};

// -------------------------------------------------
// PYBIND11
// -------------------------------------------------
PYBIND11_MODULE(Predictive_Coding_cpp, module)
{
    namespace py = pybind11;

    py::class_<MultiLayerPredictiveCodingNetwork>(
        module,
        "MultiLayerPredictiveCodingNetwork"
    )
        .def(
            py::init<
            std::vector<int>,
            double,
            py::object,
            py::object,
            py::object
            >(),
            py::arg("layer_sizes"),
            py::arg("learningRate") = 0.01,
            py::arg("variances") = py::none(),
            py::arg("paramLearningRate") = py::none(),
            py::arg("seed") = py::none()
        )

        .def(
            "train",
            &MultiLayerPredictiveCodingNetwork::train,
            py::arg("dataset"),
            py::arg("epochs") = 40,
            py::arg("steps") = 30,
            py::arg("shuffle") = true
        )

        .def(
            "predict",
            &MultiLayerPredictiveCodingNetwork::predict,
            py::arg("inputData"),
            py::arg("steps") = 50
        )

        .def(
            "getInputVariances",
            &MultiLayerPredictiveCodingNetwork::getInputVariances
        );
}
