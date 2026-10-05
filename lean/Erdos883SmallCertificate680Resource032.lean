import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_32 :
    (List.ofFn coreChunks680_32).flatten =
      (coreData680.take (coreResources680 32).q).drop 150 := by
  decide +kernel

theorem coreCheck680_32 :
    ∀ c : Fin 1, (coreChunks680_32 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 32)) = true := by
  decide +kernel
#print axioms coreFlatten680_32
#print axioms coreCheck680_32
end Erdos883Verified
