import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_13 :
    (List.ofFn coreChunks680_13).flatten =
      (coreData680.take (coreResources680 13).q).drop 127 := by
  decide +kernel

theorem coreCheck680_13 :
    ∀ c : Fin 1, (coreChunks680_13 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 13)) = true := by
  decide +kernel
#print axioms coreFlatten680_13
#print axioms coreCheck680_13
end Erdos883Verified
