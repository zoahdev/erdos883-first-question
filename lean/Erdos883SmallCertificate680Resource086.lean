import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten680_86 :
    (List.ofFn coreChunks680_86).flatten =
      (coreData680.take (coreResources680 86).q).drop 157 := by
  decide +kernel

theorem coreCheck680_86 :
    ∀ c : Fin 1, (coreChunks680_86 c).all
      (coreResourceRowCheck 619 coreData680 (coreResources680 86)) = true := by
  decide +kernel
#print axioms coreFlatten680_86
#print axioms coreCheck680_86
end Erdos883Verified
