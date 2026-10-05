import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten509_69 :
    (List.ofFn coreChunks509_69).flatten =
      (coreData509.take (coreResources509 69).q).drop 128 := by
  decide +kernel

theorem coreCheck509_69 :
    ∀ c : Fin 1, (coreChunks509_69 c).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 69)) = true := by
  decide +kernel
#print axioms coreFlatten509_69
#print axioms coreCheck509_69
end Erdos883Verified
