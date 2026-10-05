import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten618_32 :
    (List.ofFn coreChunks618_32).flatten =
      (coreData618.take (coreResources618 32).q).drop 148 := by
  decide +kernel

theorem coreCheck618_32 :
    ∀ c : Fin 1, (coreChunks618_32 c).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 32)) = true := by
  decide +kernel
#print axioms coreFlatten618_32
#print axioms coreCheck618_32
end Erdos883Verified
