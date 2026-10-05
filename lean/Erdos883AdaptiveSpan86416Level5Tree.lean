import Erdos883AdaptiveSpan86416Level5TreeData
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified
theorem adaptiveNumericSpansLength86416_5 : adaptiveNumericSpans86416_5.length = 610 := by decide +kernel
theorem adaptiveSpanEvenCache86416_5 : adaptiveSpanEven86416_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanEvenDomain86416_5 : adaptiveSpanEven86416_5.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanEvenEntries86416_5 : adaptiveSpanEven86416_5.spans = coreEvenSpans 43208 0 adaptiveNumericSpans86416_5 := by
  decide +kernel
theorem adaptiveSpanWholeCache86416_5 : adaptiveSpanWhole86416_5.cacheCheck = true := by decide +kernel
theorem adaptiveSpanWholeDomain86416_5 : adaptiveSpanWhole86416_5.domainCheck 43208 = true := by decide +kernel
theorem adaptiveSpanWholeEntries86416_5 : adaptiveSpanWhole86416_5.spans = coreWholeSpans 0 adaptiveNumericSpans86416_5 := by
  decide +kernel
end Erdos883Verified
