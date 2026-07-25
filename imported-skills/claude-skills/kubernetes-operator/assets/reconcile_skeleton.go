// Reconcile skeleton — passes reconcile_lint.py.
// Replace <PLACEHOLDER> markers; rename receiver + types to match your CR.
package controllers

import (
	"context"
	"errors"
	"time"

	apierrors "k8s.io/apimachinery/pkg/api/errors"
	"k8s.io/apimachinery/pkg/api/meta"
	metav1 "k8s.io/apimachinery/pkg/apis/meta/v1"
	ctrl "sigs.k8s.io/controller-runtime"
	"sigs.k8s.io/controller-runtime/pkg/client"
	"sigs.k8s.io/controller-runtime/pkg/controller/controllerutil"
	"sigs.k8s.io/controller-runtime/pkg/log"
	"sigs.k8s.io/controller-runtime/pkg/predicate"

	appsv1alpha1 "<MODULE>/api/v1alpha1"
)

const finalizerName = "<group>/finalizer"

type MyAppReconciler struct {
	client.Client
	Scheme *runtime.Scheme
}

func (r *MyAppReconciler) Reconcile(ctx context.Context, req ctrl.Request) (ctrl.Result, error) {
	logger := log.FromContext(ctx).WithValues("myapp", req.NamespacedName)

	var cr appsv1alpha1.MyApp
	if err := r.Get(ctx, req.NamespacedName, &cr); err != nil {
		if apierrors.IsNotFound(err) {
			return ctrl.Result{}, nil
		}
		return ctrl.Result{}, err
	}

	if !cr.DeletionTimestamp.IsZero() {
		return r.reconcileDelete(ctx, &cr)
	}

	if !controllerutil.ContainsFinalizer(&cr, finalizerName) {
		controllerutil.AddFinalizer(&cr, finalizerName)
		return ctrl.Result{}, r.Update(ctx, &cr)
	}

	meta.SetStatusCondition(&cr.Status.Conditions, metav1.Condition{
		Type:               "Reconciling",
		Status:             metav1.ConditionTrue,
		Reason:             "InProgress",
		Message:            "Converging to desired state",
		ObservedGeneration: cr.Generation,
	})

	res, recErr := r.reconcileNormal(ctx, &cr)

	if recErr == nil {
		meta.SetStatusCondition(&cr.Status.Conditions, metav1.Condition{
			Type: "Ready", Status: metav1.ConditionTrue,
			Reason: "AllReady", Message: "all components healthy",
			ObservedGeneration: cr.Generation,
		})
	} else {
		meta.SetStatusCondition(&cr.Status.Conditions, metav1.Condition{
			Type: "Ready", Status: metav1.ConditionFalse,
			Reason: "ReconcileError", Message: recErr.Error(),
			ObservedGeneration: cr.Generation,
		})
	}

	cr.Status.ObservedGeneration = cr.Generation

	if statusErr := r.Status().Update(ctx, &cr); statusErr != nil {
		logger.Error(statusErr, "failed to update status")
		return res, errors.Join(recErr, statusErr)
	}
	return res, recErr
}

func (r *MyAppReconciler) reconcileNormal(ctx context.Context, cr *appsv1alpha1.MyApp) (ctrl.Result, error) {
	// Idempotent: read desired, build child, CreateOrUpdate.
	deployment := &appsv1.Deployment{ObjectMeta: metav1.ObjectMeta{Name: cr.Name, Namespace: cr.Namespace}}
	op, err := controllerutil.CreateOrUpdate(ctx, r.Client, deployment, func() error {
		deployment.Spec.Replicas = &cr.Spec.Replicas
		// Build container spec from cr.Spec — extracted helper for clarity
		// deployment.Spec.Template.Spec.Containers = buildContainers(&cr.Spec)
		return controllerutil.SetControllerReference(cr, deployment, r.Scheme)
	})
	if err != nil {
		return ctrl.Result{}, err
	}
	log.FromContext(ctx).Info("deployment", "operation", op)

	// Periodic resync — keeps status fresh even when nothing changes.
	return ctrl.Result{RequeueAfter: 5 * time.Minute}, nil
}

func (r *MyAppReconciler) reconcileDelete(ctx context.Context, cr *appsv1alpha1.MyApp) (ctrl.Result, error) {
	if !controllerutil.ContainsFinalizer(cr, finalizerName) {
		return ctrl.Result{}, nil
	}
	if err := r.deleteExternalResources(ctx, cr); err != nil {
		return ctrl.Result{RequeueAfter: 30 * time.Second}, err
	}
	controllerutil.RemoveFinalizer(cr, finalizerName)
	return ctrl.Result{}, r.Update(ctx, cr)
}

func (r *MyAppReconciler) deleteExternalResources(ctx context.Context, cr *appsv1alpha1.MyApp) error {
	// Implement teardown of external state (cloud DB, S3 bucket, DNS record, ...)
	return nil
}

func (r *MyAppReconciler) SetupWithManager(mgr ctrl.Manager) error {
	return ctrl.NewControllerManagedBy(mgr).
		For(&appsv1alpha1.MyApp{}).
		Owns(&appsv1.Deployment{}).
		WithEventFilter(predicate.GenerationChangedPredicate{}).
		Complete(r)
}
