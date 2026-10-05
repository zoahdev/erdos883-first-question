import Erdos883AdaptiveSpan86416Level0TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_0 : adaptiveNumericSpans86416_0.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_0 : adaptiveSpanEven86416_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_0 : adaptiveSpanEven86416_0.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_0 : adaptiveSpanEven86416_0.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_0 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_0 : adaptiveSpanWhole86416_0.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_0 : adaptiveSpanWhole86416_0.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_0 : adaptiveSpanWhole86416_0.spans = coreWholeSpans 0 adaptiveNumericSpans86416_0 := by
  decide +kernel
end Erdos883Verified
