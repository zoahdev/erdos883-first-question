import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_30 :
    (List.ofFn coreChunks509_30).flatten =
      (coreData509.take (coreResources509 30).q).drop 125 := by
  decide +kernel

theorem coreCheck509_30 :
    ∀ c : Fin 1, (coreChunks509_30 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 30)) = true := by
  decide +kernel
#print axioms coreFlatten509_30
#print axioms coreCheck509_30
end Erdos883Verified
