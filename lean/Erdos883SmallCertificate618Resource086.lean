import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_86 :
    (List.ofFn coreChunks618_86).flatten =
      (coreData618.take (coreResources618 86).q).drop 177 := by
  decide +kernel

theorem coreCheck618_86 :
    ∀ c : Fin 1, (coreChunks618_86 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 86)) = true := by
  decide +kernel
#print axioms coreFlatten618_86
#print axioms coreCheck618_86
end Erdos883Verified
